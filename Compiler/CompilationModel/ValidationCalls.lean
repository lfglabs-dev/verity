/- 
  Compiler.CompilationModel.ValidationCalls: Call graph and identifier validation
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.AbiTypeLayout
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.InternalArgs
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.IssueRefs
import Compiler.CompilationModel.ScopeValidation
import Compiler.CompilationModel.UsageAnalysis

namespace Compiler.CompilationModel

def reservedExternalNames
    (mappingHelpersRequired arrayHelpersRequired arrayElementWordHelpersRequired
      paramDynamicHeadWordHelpersRequired
      mulDiv512HelpersRequired
      storageArrayHelpersRequired dynamicBytesEqHelpersRequired
      checkedArithmeticHelpersRequired : Bool) : List String :=
  let mappingHelpers := if mappingHelpersRequired then ["mappingSlot"] else []
  let arrayHelpers :=
    if arrayHelpersRequired then
      [ checkedArrayElementCalldataHelperName
      , checkedArrayElementMemoryHelperName
      ]
    else
      []
  let arrayElementWordHelpers :=
    if arrayElementWordHelpersRequired then
      [ checkedArrayElementWordCalldataHelperName
      , checkedArrayElementWordMemoryHelperName
      , checkedArrayElementDynamicWordCalldataHelperName
      , checkedArrayElementDynamicWordMemoryHelperName
      , checkedArrayElementDynamicDataOffsetCalldataHelperName
      , checkedArrayElementDynamicDataOffsetMemoryHelperName
      ]
    else
      []
  let paramDynamicHeadWordHelpers :=
    if paramDynamicHeadWordHelpersRequired then
      [ checkedParamDynamicHeadWordCalldataHelperName
      , checkedParamDynamicHeadWordMemoryHelperName
      , checkedParamDynamicMemberLengthCalldataHelperName
      , checkedParamDynamicMemberLengthMemoryHelperName
      , checkedParamDynamicMemberDataOffsetCalldataHelperName
      , checkedParamDynamicMemberDataOffsetMemoryHelperName
      , checkedParamDynamicMemberElementCalldataHelperName
      , checkedParamDynamicMemberElementMemoryHelperName
      ]
    else
      []
  let mulDiv512Helpers :=
    if mulDiv512HelpersRequired then
      [ fullMulDivHelperName
      , fullMulDivUpHelperName
      ]
    else
      []
  let storageArrayHelpers :=
    if storageArrayHelpersRequired then
      [checkedStorageArrayElementHelperName]
    else
      []
  let dynamicBytesEqHelpers :=
    if dynamicBytesEqHelpersRequired then
      [dynamicBytesEqCalldataHelperName, dynamicBytesEqMemoryHelperName]
    else
      []
  let checkedArithmeticHelpers :=
    if checkedArithmeticHelpersRequired then
      [ checkedAddUint256HelperName
      , checkedSubUint256HelperName
      , checkedMulUint256HelperName
      , checkedDivUint256HelperName
      , panicError0x11HelperName
      , panicError0x12HelperName
      ]
    else
      []
  let builtins := [builtinExpName]
  let entrypoints := ["fallback", "receive"]
  (mappingHelpers ++ arrayHelpers ++ arrayElementWordHelpers ++ paramDynamicHeadWordHelpers ++ mulDiv512Helpers ++ storageArrayHelpers ++ dynamicBytesEqHelpers ++ checkedArithmeticHelpers ++ builtins ++ entrypoints).eraseDups

def firstReservedExternalCollision
    (spec : CompilationModel)
    (mappingHelpersRequired arrayHelpersRequired arrayElementWordHelpersRequired
      paramDynamicHeadWordHelpersRequired
      mulDiv512HelpersRequired
      storageArrayHelpersRequired dynamicBytesEqHelpersRequired
      checkedArithmeticHelpersRequired : Bool) : Option String :=
  (spec.externals.map (·.name)).find? (fun name =>
    name.startsWith internalFunctionPrefix ||
      (reservedExternalNames
        mappingHelpersRequired
        arrayHelpersRequired
        arrayElementWordHelpersRequired
        paramDynamicHeadWordHelpersRequired
        mulDiv512HelpersRequired
        storageArrayHelpersRequired
        dynamicBytesEqHelpersRequired
        checkedArithmeticHelpersRequired).contains name)

def internalDynamicParamSupported : ParamType → Bool
  | ParamType.array _ => true
  | ParamType.bytes | ParamType.string => true
  | ty@(ParamType.tuple _) => isDynamicParamType ty
  | ty@(ParamType.fixedArray _ _) => isDynamicParamType ty
  | ParamType.newtypeOf _ baseTy => internalDynamicParamSupported baseTy
  | _ => false

def firstUnsupportedInternalDynamicParam
    (fns : List FunctionSpec) : Option (String × String × ParamType) :=
  let rec goFns : List FunctionSpec → Option (String × String × ParamType)
    | [] => none
    | fn :: rest =>
        if !fn.isInternal then
          goFns rest
        else
          match fn.params.find? (fun p => isDynamicParamType p.ty && !internalDynamicParamSupported p.ty) with
          | some p => some (fn.name, p.name, p.ty)
          | none => goFns rest
  goFns fns

def internalCallYulArgCountForParam : ParamType → Nat
  | ParamType.array _ => 2
  | ParamType.bytes | ParamType.string => 2
  | ty@(ParamType.fixedArray _ _) =>
      if isDynamicParamType ty then 1 else (staticParamBindingNames "__arg" ty).length
  | ty@(ParamType.tuple _) =>
      if isDynamicParamType ty then 1 else (staticParamBindingNames "__arg" ty).length
  | ParamType.newtypeOf _ baseTy =>
      internalCallYulArgCountForParam baseTy
  | _ => 1

def internalCallYulArgCount (params : List Param) : Nat :=
  params.foldl (fun acc param => acc + internalCallYulArgCountForParam param.ty) 0

def internalReturnYulCountForType : ParamType → Nat
  | ParamType.array _ => 2
  | _ => 1

def internalReturnYulCount (returns : List ParamType) : Nat :=
  returns.foldl (fun acc retTy => acc + internalReturnYulCountForType retTy) 0

def linkedExternalCallYulArgCountForParam : ParamType → Nat
  | ParamType.array elemTy => if isSingleWordStaticParamType elemTy then 2 else 1
  | ParamType.bytes | ParamType.string => 2
  | _ => 1

def linkedExternalCallYulArgCount (params : List ParamType) : Nat :=
  params.foldl (fun acc paramTy => acc + linkedExternalCallYulArgCountForParam paramTy) 0

def linkedExternalReturnYulCountForType : ParamType → Nat
  | ParamType.tuple elemTys =>
      elemTys.foldl (fun acc elemTy => acc + linkedExternalReturnYulCountForType elemTy) 0
  | ParamType.fixedArray elemTy size =>
      size * linkedExternalReturnYulCountForType elemTy
  | _ => 1

def linkedExternalReturnYulCount (returns : List ParamType) : Nat :=
  returns.foldl (fun acc retTy => acc + linkedExternalReturnYulCountForType retTy) 0

def findInternalFunctionByName (functions : List FunctionSpec)
    (callerName calleeName : String) : Except String FunctionSpec := do
  let candidates := functions.filter (fun fn => fn.isInternal && fn.name == calleeName)
  match candidates with
  | [fn] => pure fn
  | [] =>
      throw s!"Compilation error: function '{callerName}' references unknown internal function '{calleeName}' ({issue625Ref})."
  | _ =>
      throw s!"Compilation error: function '{callerName}' references ambiguous internal function '{calleeName}' ({issue625Ref})."

def internalParamTypeAndLayoutMatches (sourceTy expectedTy : ParamType) : Bool :=
  sourceTy == expectedTy &&
    internalCallYulArgNamesForParam "__arg" { name := "__arg", ty := sourceTy } ==
      internalCallYulArgNamesForParam "__arg" { name := "__arg", ty := expectedTy }

partial def dynamicMemberTypeAtWordOffset : ParamType → Nat → Option ParamType
  | ParamType.tuple elemTys, wordOffset =>
      let rec goTuple : List ParamType → Nat → Option ParamType
        | [], _ => none
        | elemTy :: rest, cursor =>
            if cursor == wordOffset then
              some elemTy
            else
              goTuple rest (cursor + paramParentHeadWords elemTy)
      goTuple elemTys 0
  | ParamType.fixedArray elemTy n, wordOffset =>
      let rec goArray : Nat → Nat → Option ParamType
        | 0, _ => none
        | count + 1, cursor =>
            if cursor == wordOffset then
              some elemTy
            else
              goArray count (cursor + paramParentHeadWords elemTy)
      goArray n 0
  | ParamType.newtypeOf _ baseTy, wordOffset =>
      dynamicMemberTypeAtWordOffset baseTy wordOffset
  | _, _ => none

def validateInternalCallArgForParam
    (callerParams : List Param) (callerName calleeName : String)
    (param : Param) (arg : Expr) : Except String Unit := do
  if isExpandedInternalParamType param.ty then
    match directForwardedInternalArgName? arg with
    | none =>
        throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with a computed argument for expanded parameter '{param.name}' ({repr param.ty}); issue #1889 currently supports direct parameter forwarding only."
    | some _ => pure ()
  else
    pure ()
  if isExpandedInternalParamType param.ty then
    match arg with
    | Expr.param sourceName =>
        match findParamType callerParams sourceName with
        | some sourceTy =>
            if internalParamTypeAndLayoutMatches sourceTy param.ty then
              pure ()
            else
              throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with parameter '{sourceName}' of type/layout {repr sourceTy}, expected {repr param.ty} for expanded callee parameter '{param.name}' (issue #1889)."
        | none =>
            throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' forwarding unknown parameter '{sourceName}' for expanded callee parameter '{param.name}' (issue #1889)."
    | _ => pure ()
  else
    pure ()

def expandedExprParamNames? : List Expr → Option (List String)
  | [] => some []
  | Expr.param name :: rest =>
      match expandedExprParamNames? rest with
      | some names => some (name :: names)
      | none => none
  | _ => none

def expandedProjectionType?
    (callerParams : List Param) : List Expr → Option ParamType
  | [ Expr.paramDynamicMemberDataOffset name wordOffset
    , Expr.paramDynamicMemberLength lengthName lengthWordOffset ] =>
      if name == lengthName && wordOffset == lengthWordOffset then
        match findParamType callerParams name with
        | some sourceTy => dynamicMemberTypeAtWordOffset sourceTy wordOffset
        | none => none
      else
        none
  | [ Expr.arrayElementDynamicMemberDataOffset name index wordOffset
    , Expr.arrayElementDynamicMemberLength lengthName lengthIndex lengthWordOffset ] =>
      let sameIndex :=
        match index, lengthIndex with
        | Expr.param lhs, Expr.param rhs => lhs == rhs
        | Expr.localVar lhs, Expr.localVar rhs => lhs == rhs
        | Expr.literal lhs, Expr.literal rhs => lhs == rhs
        | _, _ => false
      if name == lengthName && sameIndex && wordOffset == lengthWordOffset then
        match findParamType callerParams name with
        | some (ParamType.array elemTy) => dynamicMemberTypeAtWordOffset elemTy wordOffset
        | some (ParamType.newtypeOf _ (ParamType.array elemTy)) =>
            dynamicMemberTypeAtWordOffset elemTy wordOffset
        | _ => none
      else
        none
  | _ => none

def expandedArgsMatchCallerParam
    (param : Param) (argNames : List String) (source : Param) : Bool :=
  internalParamTypeAndLayoutMatches source.ty param.ty &&
    argNames == internalCallYulArgNamesForParam source.name param

def validateExpandedInternalCallArgNames
    (callerParams : List Param) (callerName calleeName : String) (param : Param) (args : List Expr) :
    Except String Unit := do
  let expectedNames := internalFunctionYulParamNames [param]
  if args.length != expectedNames.length then
    throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with {args.length} expanded arg(s) for parameter '{param.name}', expected {expectedNames.length} ({issue625Ref}, issue #1889)."
  else
    match expandedExprParamNames? args with
    | some argNames =>
        if callerParams.any (expandedArgsMatchCallerParam param argNames) then
          pure ()
        else
          throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with expanded args {repr argNames} for parameter '{param.name}', but no caller parameter has exact type/layout {repr param.ty} and matching generated names (issue #1889)."
    | none =>
        match expandedProjectionType? callerParams args with
        | some sourceTy =>
            if internalParamTypeAndLayoutMatches sourceTy param.ty then
              pure ()
            else
              throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with projected expanded args of type/layout {repr sourceTy}, expected {repr param.ty} for parameter '{param.name}' (issue #1889)."
        | none =>
            throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with non-parameter expanded args for parameter '{param.name}' without a checked projection proving exact type/layout forwarding (issue #1889)."

def validateExpandedInternalCallArgs
    (callerParams : List Param) (callerName calleeName : String) : List Param → List Expr → Except String Unit
  | [], [] => pure ()
  | param :: params, args => do
      let expectedCount := (internalFunctionYulParamNames [param]).length
      let head := args.take expectedCount
      let tail := args.drop expectedCount
      validateExpandedInternalCallArgNames callerParams callerName calleeName param head
      validateExpandedInternalCallArgs callerParams callerName calleeName params tail
  | [], _ :: _ =>
      throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with extra expanded arg(s) after exact type/layout validation ({issue625Ref}, issue #1889)."

def validateInternalCallSourceArgs
    (callerParams : List Param) (callerName calleeName : String)
    (params : List Param) (args : List Expr) : Except String Unit := do
  let expandedArgCount :=
    params.foldl (fun acc param => acc + (internalFunctionYulParamNames [param]).length) 0
  if args.length == expandedArgCount && args.length != params.length then
    validateExpandedInternalCallArgs callerParams callerName calleeName params args
  else if args.length != params.length then
    throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with {args.length} source arg(s), expected {params.length} (or {expandedArgCount} exact expanded Yul arg(s) for legacy call sites) ({issue625Ref}, issue #1889)."
  else
    let rec go : List Param → List Expr → Except String Unit
      | [], [] => pure ()
      | param :: params, arg :: args => do
          validateInternalCallArgForParam callerParams callerName calleeName param arg
          go params args
      | _, _ => pure ()
    go params args

/-- Node-local check: shape of an `Expr.internalCall` node. Operands are
    reached via the canonical post-order `Expr.forDeepPostM`, matching the old
    walk which validated arguments before the call's own arity/return shape. -/
def validateInternalCallShapesNodeExpr
    (functions : List FunctionSpec) (callerName : String) (callerParams : List Param) : Expr → Except String Unit
  | Expr.internalCall calleeName args => do
      let callee ← findInternalFunctionByName functions callerName calleeName
      validateInternalCallSourceArgs callerParams callerName calleeName callee.params args
      let returns ← functionReturns callee
      if returns.length != 1 || internalReturnYulCount returns != 1 then
        throw s!"Compilation error: function '{callerName}' uses Expr.internalCall '{calleeName}' but callee returns {returns.length} logical value(s) / {internalReturnYulCount returns} Yul value(s); use Stmt.internalCallAssign for multi-return calls ({issue625Ref})."
  | _ => pure ()

def validateInternalCallShapesInExpr
    (functions : List FunctionSpec) (callerName : String) (callerParams : List Param) (e : Expr) : Except String Unit :=
  e.forDeepPostM (validateInternalCallShapesNodeExpr functions callerName callerParams)

def validateInternalCallShapesInExprList
    (functions : List FunctionSpec) (callerName : String) (callerParams : List Param) (es : List Expr) : Except String Unit :=
  es.forM (validateInternalCallShapesInExpr functions callerName callerParams)

/-- Node-local statement check: validates the statement's own expressions and
    internal-call shape; nested statement bodies are reached via the canonical
    `Stmt.forDeepM`. `returnArray`/`returnBytes`/`returnStorageWords`/
    `returnCodeData` deliberately contribute nothing here (as in the old walk). -/
def validateInternalCallShapesNodeStmt
    (functions : List FunctionSpec) (callerName : String) (callerParams : List Param) : Stmt → Except String Unit
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value
  | Stmt.setStorageWord _ _ value |
    Stmt.storageArrayPush _ value |
    Stmt.return value | Stmt.require value _ =>
      validateInternalCallShapesInExpr functions callerName callerParams value
  | Stmt.setStorageArrayElement _ index value => do
      validateInternalCallShapesInExpr functions callerName callerParams index
      validateInternalCallShapesInExpr functions callerName callerParams value
  | Stmt.storageArrayPop _ =>
      pure ()
  | Stmt.requireError cond _ args => do
      validateInternalCallShapesInExpr functions callerName callerParams cond
      validateInternalCallShapesInExprList functions callerName callerParams args
  | Stmt.revertError _ args =>
      validateInternalCallShapesInExprList functions callerName callerParams args
  | .panicCode code =>
      validateInternalCallShapesInExpr functions callerName callerParams code
  | Stmt.mstore offset value | Stmt.tstore offset value => do
      validateInternalCallShapesInExpr functions callerName callerParams offset
      validateInternalCallShapesInExpr functions callerName callerParams value
  | Stmt.calldatacopy destOffset sourceOffset size
  | Stmt.returndataCopy destOffset sourceOffset size => do
      validateInternalCallShapesInExpr functions callerName callerParams destOffset
      validateInternalCallShapesInExpr functions callerName callerParams sourceOffset
      validateInternalCallShapesInExpr functions callerName callerParams size
  | Stmt.revertReturndata =>
      pure ()
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value => do
      validateInternalCallShapesInExpr functions callerName callerParams key
      validateInternalCallShapesInExpr functions callerName callerParams value
  | Stmt.setMappingChain _ keys value => do
      validateInternalCallShapesInExprList functions callerName callerParams keys
      validateInternalCallShapesInExpr functions callerName callerParams value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value => do
      validateInternalCallShapesInExpr functions callerName callerParams key1
      validateInternalCallShapesInExpr functions callerName callerParams key2
      validateInternalCallShapesInExpr functions callerName callerParams value
  | Stmt.ite cond _ _ =>
      validateInternalCallShapesInExpr functions callerName callerParams cond
  | Stmt.forEach _ count _ =>
      validateInternalCallShapesInExpr functions callerName callerParams count
  | Stmt.unsafeBlock _ _ =>
      pure ()
  | Stmt.matchAdt _ scrutinee _ =>
      validateInternalCallShapesInExpr functions callerName callerParams scrutinee
  | Stmt.emit _ args =>
      validateInternalCallShapesInExprList functions callerName callerParams args
  | Stmt.returnValues values =>
      validateInternalCallShapesInExprList functions callerName callerParams values
  | Stmt.internalCall calleeName args => do
      validateInternalCallShapesInExprList functions callerName callerParams args
      let callee ← findInternalFunctionByName functions callerName calleeName
      validateInternalCallSourceArgs callerParams callerName calleeName callee.params args
      let returns ← functionReturns callee
      if !returns.isEmpty then
        throw s!"Compilation error: function '{callerName}' uses Stmt.internalCall '{calleeName}' but callee returns {returns.length} values; use Expr.internalCall for single-return or Stmt.internalCallAssign for multi-return calls ({issue625Ref})."
  | Stmt.internalCallAssign names calleeName args => do
      if names.isEmpty then
        throw s!"Compilation error: function '{callerName}' uses Stmt.internalCallAssign with no target variables ({issue625Ref})."
      let rec firstDuplicateTarget (seen : List String) : List String → Option String
        | [] => none
        | name :: rest =>
            if seen.contains name then
              some name
            else
              firstDuplicateTarget (name :: seen) rest
      match firstDuplicateTarget [] names with
      | some dup =>
          throw s!"Compilation error: function '{callerName}' uses Stmt.internalCallAssign with duplicate target '{dup}' ({issue625Ref})."
      | none =>
          pure ()
      validateInternalCallShapesInExprList functions callerName callerParams args
      let callee ← findInternalFunctionByName functions callerName calleeName
      validateInternalCallSourceArgs callerParams callerName calleeName callee.params args
      let returns ← functionReturns callee
      let expectedReturns := internalReturnYulCount returns
      if expectedReturns != names.length then
        throw s!"Compilation error: function '{callerName}' binds {names.length} Yul value(s) from internal function '{calleeName}', but callee returns {returns.length} logical value(s) / {expectedReturns} Yul value(s) ({issue625Ref})."
  | Stmt.rawLog topics dataOffset dataSize => do
      validateInternalCallShapesInExprList functions callerName callerParams topics
      validateInternalCallShapesInExpr functions callerName callerParams dataOffset
      validateInternalCallShapesInExpr functions callerName callerParams dataSize
  | Stmt.externalCallBind _resultVars _ args =>
      validateInternalCallShapesInExprList functions callerName callerParams args
  | Stmt.tryExternalCallBind _ _resultVars _ args =>
      validateInternalCallShapesInExprList functions callerName callerParams args
  | Stmt.ecm _ args =>
      validateInternalCallShapesInExprList functions callerName callerParams args
  | _ =>
      pure ()

def validateInternalCallShapesInStmt
    (functions : List FunctionSpec) (callerName : String) (callerParams : List Param)
    (stmt : Stmt) : Except String Unit :=
  stmt.forDeepM (validateInternalCallShapesNodeStmt functions callerName callerParams)

def validateInternalCallShapesInStmtList
    (functions : List FunctionSpec) (callerName : String) (callerParams : List Param)
    (stmts : List Stmt) : Except String Unit :=
  Stmt.forDeepListM (validateInternalCallShapesNodeStmt functions callerName callerParams) stmts

def validateInternalCallShapesInMatchBranches
    (functions : List FunctionSpec) (callerName : String) (callerParams : List Param)
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  branches.forM fun (_, _, body) =>
    validateInternalCallShapesInStmtList functions callerName callerParams body

def validateInternalCallShapesInFunction (functions : List FunctionSpec)
    (spec : FunctionSpec) : Except String Unit := do
  spec.body.forM (validateInternalCallShapesInStmt functions spec.name spec.params)

/-- Node-local check: shape of an `Expr.externalCall` node. Operands are
    reached via the canonical pre-order `Expr.forDeepM`, matching the old walk
    which checked the call's own shape before its arguments. -/
def validateExternalCallTargetsNodeExpr
    (externals : List ExternalFunction) (context : String) : Expr → Except String Unit
  | Expr.externalCall name args => do
      if name == builtinExpName then
        if args.length != 2 then
          throw s!"Compilation error: {context} calls builtin exp with {args.length} args, expected 2."
      else
        match externals.find? (fun ext => ext.name == name) with
        | none =>
            throw s!"Compilation error: {context} references unknown external call target '{name}' ({issue732Ref}). Declare it in spec.externals."
        | some ext =>
            let expectedArgs := linkedExternalCallYulArgCount ext.params
            if args.length != expectedArgs then
              throw s!"Compilation error: {context} calls external '{name}' with {args.length} Yul arg(s), expected {expectedArgs} ({issue184Ref})."
            let returns ← externalFunctionReturns ext
            if returns.length != 1 then
              throw s!"Compilation error: {context} uses Expr.externalCall '{name}' but spec.externals declares {returns.length} return values; Expr.externalCall requires exactly 1 ({issue184Ref})."
  | _ => pure ()

def validateExternalCallTargetsInExpr
    (externals : List ExternalFunction) (context : String) (e : Expr) : Except String Unit :=
  e.forDeepM (validateExternalCallTargetsNodeExpr externals context)

def validateExternalCallTargetsInExprList
    (externals : List ExternalFunction) (context : String) (es : List Expr) : Except String Unit :=
  es.forM (validateExternalCallTargetsInExpr externals context)

/-- Node-local statement check: validates the statement's own expressions and
    external-call binding shape; nested statement bodies are reached via the
    canonical `Stmt.forDeepM`. `returnArray`/`returnBytes`/`returnStorageWords`/
    `returnCodeData` deliberately contribute nothing here (as in the old walk). -/
def validateExternalCallTargetsNodeStmt
    (externals : List ExternalFunction) (context : String) : Stmt → Except String Unit
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value
  | Stmt.setStorageWord _ _ value |
    Stmt.storageArrayPush _ value |
    Stmt.return value | Stmt.require value _ =>
      validateExternalCallTargetsInExpr externals context value
  | Stmt.setStorageArrayElement _ index value => do
      validateExternalCallTargetsInExpr externals context index
      validateExternalCallTargetsInExpr externals context value
  | Stmt.storageArrayPop _ =>
      pure ()
  | Stmt.requireError cond _ args => do
      validateExternalCallTargetsInExpr externals context cond
      validateExternalCallTargetsInExprList externals context args
  | Stmt.revertError _ args =>
      validateExternalCallTargetsInExprList externals context args
  | .panicCode code =>
      validateExternalCallTargetsInExpr externals context code
  | Stmt.mstore offset value | Stmt.tstore offset value => do
      validateExternalCallTargetsInExpr externals context offset
      validateExternalCallTargetsInExpr externals context value
  | Stmt.calldatacopy destOffset sourceOffset size
  | Stmt.returndataCopy destOffset sourceOffset size => do
      validateExternalCallTargetsInExpr externals context destOffset
      validateExternalCallTargetsInExpr externals context sourceOffset
      validateExternalCallTargetsInExpr externals context size
  | Stmt.revertReturndata =>
      pure ()
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value => do
      validateExternalCallTargetsInExpr externals context key
      validateExternalCallTargetsInExpr externals context value
  | Stmt.setMappingChain _ keys value => do
      validateExternalCallTargetsInExprList externals context keys
      validateExternalCallTargetsInExpr externals context value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value => do
      validateExternalCallTargetsInExpr externals context key1
      validateExternalCallTargetsInExpr externals context key2
      validateExternalCallTargetsInExpr externals context value
  | Stmt.ite cond _ _ =>
      validateExternalCallTargetsInExpr externals context cond
  | Stmt.forEach _ count _ =>
      validateExternalCallTargetsInExpr externals context count
  | Stmt.unsafeBlock _ _ =>
      pure ()
  | Stmt.matchAdt _ scrutinee _ =>
      validateExternalCallTargetsInExpr externals context scrutinee
  | Stmt.emit _ args =>
      validateExternalCallTargetsInExprList externals context args
  | Stmt.internalCall _ args =>
      validateExternalCallTargetsInExprList externals context args
  | Stmt.internalCallAssign _ _ args =>
      validateExternalCallTargetsInExprList externals context args
  | Stmt.externalCallBind resultVars externalName args => do
      validateExternalCallTargetsInExprList externals context args
      match externals.find? (fun ext => ext.name == externalName) with
      | none =>
          throw s!"Compilation error: {context} uses Stmt.externalCallBind with unknown external function '{externalName}'."
      | some ext => do
          let expectedArgs := linkedExternalCallYulArgCount ext.params
          if args.length != expectedArgs then
            throw s!"Compilation error: {context} calls external function '{externalName}' with {args.length} Yul arg(s), expected {expectedArgs}."
          let returns ← externalFunctionReturns ext
          let expectedReturns := linkedExternalReturnYulCount returns
          if expectedReturns != resultVars.length then
            throw s!"Compilation error: {context} binds {resultVars.length} Yul value(s) from external function '{externalName}', but it returns {expectedReturns} Yul value(s)."
          let rec checkDuplicateVars (seen : List String) : List String → Except String Unit
            | [] => pure ()
            | name :: rest =>
                if seen.contains name then
                  throw s!"Compilation error: {context} uses Stmt.externalCallBind with duplicate result variable '{name}'."
                else
                  checkDuplicateVars (name :: seen) rest
          checkDuplicateVars [] resultVars
  | Stmt.tryExternalCallBind successVar resultVars externalName args => do
      validateExternalCallTargetsInExprList externals context args
      match externals.find? (fun ext => ext.name == externalName) with
      | none =>
          throw s!"Compilation error: {context} uses Stmt.tryExternalCallBind with unknown external function '{externalName}'."
      | some ext => do
          let expectedArgs := linkedExternalCallYulArgCount ext.params
          if args.length != expectedArgs then
            throw s!"Compilation error: {context} calls external function '{externalName}' with {args.length} Yul arg(s), expected {expectedArgs}."
          let returns ← externalFunctionReturns ext
          let expectedReturns := linkedExternalReturnYulCount returns
          if expectedReturns != resultVars.length then
            throw s!"Compilation error: {context} binds {resultVars.length} Yul value(s) from external function '{externalName}', but it returns {expectedReturns} Yul value(s)."
          let tryName := s!"{externalName}_try"
          match externals.find? (fun candidate => candidate.name == tryName) with
          | none =>
              throw s!"Compilation error: {context} uses Stmt.tryExternalCallBind for external function '{externalName}', but required linked wrapper '{tryName}' is not declared."
          | some tryExt => do
              if tryExt.params != ext.params then
                throw s!"Compilation error: try wrapper '{tryName}' must take the same parameters as external function '{externalName}'."
              let tryReturns ← externalFunctionReturns tryExt
              let validTryReturns :=
                match tryReturns with
                | ParamType.bool :: tryTail =>
                    linkedExternalReturnYulCount tryTail == linkedExternalReturnYulCount returns
                | _ => false
              if !validTryReturns then
                throw s!"Compilation error: try wrapper '{tryName}' must return Bool followed by the flattened return values of external function '{externalName}'."
          let allVars := successVar :: resultVars
          let rec checkDuplicateTryVars (seen : List String) : List String → Except String Unit
            | [] => pure ()
            | name :: rest =>
                if seen.contains name then
                  throw s!"Compilation error: {context} uses Stmt.tryExternalCallBind with duplicate result variable '{name}'."
                else
                  checkDuplicateTryVars (name :: seen) rest
          checkDuplicateTryVars [] allVars
  | Stmt.returnValues values =>
      validateExternalCallTargetsInExprList externals context values
  | Stmt.rawLog topics dataOffset dataSize => do
      validateExternalCallTargetsInExprList externals context topics
      validateExternalCallTargetsInExpr externals context dataOffset
      validateExternalCallTargetsInExpr externals context dataSize
  | Stmt.ecm _ args =>
      validateExternalCallTargetsInExprList externals context args
  | _ =>
      pure ()

def validateExternalCallTargetsInStmt
    (externals : List ExternalFunction) (context : String) (stmt : Stmt) : Except String Unit :=
  stmt.forDeepM (validateExternalCallTargetsNodeStmt externals context)

def validateExternalCallTargetsInStmtList
    (externals : List ExternalFunction) (context : String) (stmts : List Stmt) : Except String Unit :=
  Stmt.forDeepListM (validateExternalCallTargetsNodeStmt externals context) stmts

def validateExternalCallTargetsInMatchBranches
    (externals : List ExternalFunction) (context : String)
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  branches.forM fun (_, _, body) =>
    validateExternalCallTargetsInStmtList externals context body

def validateExternalCallTargetsInFunction
    (externals : List ExternalFunction) (spec : FunctionSpec) : Except String Unit := do
  spec.body.forM (validateExternalCallTargetsInStmt externals s!"function '{spec.name}'")

def validateExternalCallTargetsInConstructor
    (externals : List ExternalFunction) (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      spec.body.forM (validateExternalCallTargetsInStmt externals "constructor")

mutual
def supportedCustomErrorParamType : ParamType → Bool
  | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.uint16 | ParamType.address | ParamType.bool | ParamType.bytes32 | ParamType.bytes | ParamType.string => true
  | ParamType.array elemTy => supportedCustomErrorParamType elemTy
  | ParamType.fixedArray elemTy _ => supportedCustomErrorParamType elemTy
  | ParamType.tuple elemTys => supportedCustomErrorParamTypes elemTys
  | ParamType.adt _ _ => true
  | ParamType.newtypeOf _ baseType => supportedCustomErrorParamType baseType
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals omega

def supportedCustomErrorParamTypes : List ParamType → Bool
  | [] => true
  | ty :: tys => supportedCustomErrorParamType ty && supportedCustomErrorParamTypes tys
termination_by tys => sizeOf tys
decreasing_by
  all_goals simp_wf
  all_goals omega
end

def validateErrorDef (err : ErrorDef) : Except String Unit := do
  for ty in err.params do
    if !supportedCustomErrorParamType ty then
      throw s!"Compilation error: custom error '{err.name}' uses unsupported dynamic parameter type {repr ty} ({issue586Ref}). Use uint256/address/bool/bytes32/bytes/string parameters."

def validateEventDef (eventDef : EventDef) : Except String Unit := do
  let indexedCount := eventDef.params.foldl
    (fun acc p => if p.kind == EventParamKind.indexed then acc + 1 else acc)
    0
  if indexedCount > 3 then
    throw s!"Compilation error: event '{eventDef.name}' has {indexedCount} indexed params; max is 3"

def ensureContractIdentifier (kind name : String) : Except String Unit := do
  match Compiler.ensureValidIdentifier kind name with
  | .ok _ => pure ()
  | .error err => throw s!"Compilation error: {err}"

private def ensureAbiInterfaceExternalIdentifier (name : String) : Except String Unit := do
  match name.splitOn "." with
  | [iface, method] => do
      ensureContractIdentifier "external interface" iface
      ensureContractIdentifier "external interface method" method
  | _ =>
      throw s!"Compilation error: external ABI declaration name must be '<Interface>.<method>': {name}"

/-- Source identifiers that lower directly to Yul variables must avoid the
compiler-reserved `__` prefix used by dispatch and scratch temporaries. -/
private def ensureNonReservedYulIdentifier (kind name : String) : Except String Unit := do
  if name.startsWith "__" then
    throw s!"Compilation error: {kind} '{name}' uses reserved compiler prefix '__' ({issue756Ref}). Rename it."

private def isInternalImmutableStorageName (name : String) : Bool :=
  name.startsWith "__immutable_"

private def validateContractIdentifiers (kind : String) : List String → Except String Unit
  | [] => pure ()
  | name :: rest => do
      ensureContractIdentifier kind name
      ensureNonReservedYulIdentifier kind name
      validateContractIdentifiers kind rest

private def validateFieldIdentifiers : List Field → Except String Unit
  | [] => pure ()
  | field :: rest => do
      ensureContractIdentifier "field" field.name
      if !isInternalImmutableStorageName field.name then
        ensureNonReservedYulIdentifier "field" field.name
      validateFieldIdentifiers rest

private def validateFunctionYulIdentifiers (fn : FunctionSpec) : Except String Unit := do
  validateContractIdentifiers "function parameter" (fn.params.map (·.name))
  validateContractIdentifiers "local binder" (collectStmtListBindNames fn.body)
  validateContractIdentifiers "assignment target" (collectStmtListAssignedNames fn.body)

def validateFunctionIdentifiers (fn : FunctionSpec) : Except String Unit := do
  ensureContractIdentifier "function" fn.name
  validateFunctionYulIdentifiers fn

private def validateConstructorYulIdentifiers (ctor : ConstructorSpec) : Except String Unit := do
  validateContractIdentifiers "constructor parameter" (ctor.params.map (·.name))
  validateContractIdentifiers "local binder" (collectStmtListBindNames ctor.body)
  for name in collectStmtListAssignedNames ctor.body do
    ensureContractIdentifier "assignment target" name
    if !isInternalImmutableStorageName name then
      ensureNonReservedYulIdentifier "assignment target" name

def validateConstructorIdentifiers (ctor : ConstructorSpec) : Except String Unit :=
  validateConstructorYulIdentifiers ctor

private def validateFunctionIdentifierList : List FunctionSpec → Except String Unit
  | [] => pure ()
  | fn :: rest => do
      validateFunctionIdentifiers fn
      validateFunctionIdentifierList rest

private def validateReservedCompilerIdentifiers (spec : CompilationModel) : Except String Unit := do
  validateFieldIdentifiers spec.fields
  validateFunctionIdentifierList spec.functions
  match spec.constructor with
  | none => pure ()
  | some ctor =>
      validateConstructorIdentifiers ctor

def validateIdentifierShapes (spec : CompilationModel) : Except String Unit := do
  ensureContractIdentifier "contract" spec.name
  validateReservedCompilerIdentifiers spec
  for eventDef in spec.events do
    ensureContractIdentifier "event" eventDef.name
    for p in eventDef.params do
      ensureContractIdentifier "event parameter" p.name
  for err in spec.errors do
    ensureContractIdentifier "custom error" err.name
  for ext in spec.externals do
    if ext.linkMode == .external && ext.name.contains '.' then
      -- Dotted ABI-interface externals (e.g. `IPool.supply`) lower by selector, never
      -- as a Yul identifier. Other external forms are linked/called by their name.
      ensureAbiInterfaceExternalIdentifier ext.name
    else
      ensureContractIdentifier "external declaration" ext.name

private theorem ensureNonReservedYulIdentifier_ok
    {kind name : String}
    (hvalidate : ensureNonReservedYulIdentifier kind name = Except.ok ()) :
    ¬ name.startsWith "__" := by
  by_cases hreserved : name.startsWith "__"
  · simp [ensureNonReservedYulIdentifier, hreserved] at hvalidate
  · exact hreserved

private theorem validateContractIdentifiers_ok_of_mem
    {kind name : String}
    {names : List String}
    (hvalidate : validateContractIdentifiers kind names = Except.ok ())
    (hmem : name ∈ names) :
    ¬ name.startsWith "__" := by
  induction names with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases hcontract : ensureContractIdentifier kind head with
      | error err =>
          simp [validateContractIdentifiers, hcontract] at hvalidate
          cases hvalidate
      | ok _ =>
          cases hreserved : ensureNonReservedYulIdentifier kind head with
          | error err =>
              simp [validateContractIdentifiers, hcontract, hreserved] at hvalidate
              cases hvalidate
          | ok _ =>
              have htail : validateContractIdentifiers kind tail = Except.ok () := by
                simp only [validateContractIdentifiers, hcontract, hreserved] at hvalidate
                exact hvalidate
              simp at hmem
              rcases hmem with rfl | hmem
              · exact ensureNonReservedYulIdentifier_ok hreserved
              · exact ih htail hmem

private theorem validateFieldIdentifiers_ok_of_mem
    {fields : List Field}
    {field : Field}
    (hvalidate : validateFieldIdentifiers fields = Except.ok ())
    (hmem : field ∈ fields) :
    ¬ (field.name.startsWith "__" && !isInternalImmutableStorageName field.name) := by
  induction fields with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases hcontract : ensureContractIdentifier "field" head.name with
      | error err =>
          simp [validateFieldIdentifiers, hcontract] at hvalidate
          cases hvalidate
      | ok _ =>
          by_cases himm : isInternalImmutableStorageName head.name
          · have htail : validateFieldIdentifiers tail = Except.ok () := by
              simp only [validateFieldIdentifiers, hcontract, himm] at hvalidate
              exact hvalidate
            simp at hmem
            rcases hmem with rfl | hmem
            · simp [himm]
            · exact ih htail hmem
          · cases hreserved : ensureNonReservedYulIdentifier "field" head.name with
            | error err =>
                simp [validateFieldIdentifiers, hcontract, himm, hreserved] at hvalidate
                cases hvalidate
            | ok _ =>
                have htail : validateFieldIdentifiers tail = Except.ok () := by
                  simp only [validateFieldIdentifiers, hcontract, himm, hreserved] at hvalidate
                  exact hvalidate
                simp at hmem
                rcases hmem with rfl | hmem
                · intro hbad
                  have hbadReserved := hbad
                  simp only [Bool.and_eq_true] at hbadReserved
                  exact (ensureNonReservedYulIdentifier_ok hreserved) hbadReserved.1
                · exact ih htail hmem

private theorem validateFunctionYulIdentifiers_params_ok_of_mem
    {fn : FunctionSpec}
    {name : String}
    (hvalidate : validateFunctionYulIdentifiers fn = Except.ok ())
    (hmem : name ∈ fn.params.map (·.name)) :
    ¬ name.startsWith "__" := by
  have hparams :
      validateContractIdentifiers "function parameter" (fn.params.map (·.name)) = Except.ok () := by
    unfold validateFunctionYulIdentifiers at hvalidate
    cases hparams : validateContractIdentifiers "function parameter" (fn.params.map (·.name)) with
    | error err =>
        simp [hparams] at hvalidate
        cases hvalidate
    | ok a =>
        cases a
        rfl
  exact validateContractIdentifiers_ok_of_mem hparams hmem

private theorem validateFunctionYulIdentifiers_locals_ok_of_mem
    {fn : FunctionSpec}
    {name : String}
    (hvalidate : validateFunctionYulIdentifiers fn = Except.ok ())
    (hmem : name ∈ collectStmtListBindNames fn.body) :
    ¬ name.startsWith "__" := by
  have hparams :
      validateContractIdentifiers "function parameter" (fn.params.map (·.name)) = Except.ok () := by
    unfold validateFunctionYulIdentifiers at hvalidate
    cases hparams : validateContractIdentifiers "function parameter" (fn.params.map (·.name)) with
    | error err =>
        simp [hparams] at hvalidate
        cases hvalidate
    | ok a =>
        cases a
        rfl
  have hlocals :
      validateContractIdentifiers "local binder" (collectStmtListBindNames fn.body) = Except.ok () := by
    unfold validateFunctionYulIdentifiers at hvalidate
    cases hlocals : validateContractIdentifiers "local binder" (collectStmtListBindNames fn.body) with
    | error err =>
        simp [hparams, hlocals] at hvalidate
        cases hvalidate
    | ok a =>
        cases a
        rfl
  exact validateContractIdentifiers_ok_of_mem hlocals hmem

private theorem validateFunctionYulIdentifiers_assignTargets_ok_of_mem
    {fn : FunctionSpec}
    {name : String}
    (hvalidate : validateFunctionYulIdentifiers fn = Except.ok ())
    (hmem : name ∈ collectStmtListAssignedNames fn.body) :
    ¬ name.startsWith "__" := by
  have hparams :
      validateContractIdentifiers "function parameter" (fn.params.map (·.name)) = Except.ok () := by
    unfold validateFunctionYulIdentifiers at hvalidate
    cases hparams : validateContractIdentifiers "function parameter" (fn.params.map (·.name)) with
    | error err =>
        simp [hparams] at hvalidate
        cases hvalidate
    | ok a =>
        cases a
        rfl
  have hlocals :
      validateContractIdentifiers "local binder" (collectStmtListBindNames fn.body) = Except.ok () := by
    unfold validateFunctionYulIdentifiers at hvalidate
    cases hlocals : validateContractIdentifiers "local binder" (collectStmtListBindNames fn.body) with
    | error err =>
        simp [hparams, hlocals] at hvalidate
        cases hvalidate
    | ok a =>
        cases a
        rfl
  have hassign :
      validateContractIdentifiers "assignment target" (collectStmtListAssignedNames fn.body) = Except.ok () := by
    unfold validateFunctionYulIdentifiers at hvalidate
    simp only [hparams, hlocals] at hvalidate
    exact hvalidate
  exact validateContractIdentifiers_ok_of_mem hassign hmem

private theorem validateFunctionIdentifierList_ok_of_mem
    {functions : List FunctionSpec}
    {fn : FunctionSpec}
    (hvalidate : validateFunctionIdentifierList functions = Except.ok ())
    (hmem : fn ∈ functions) :
    validateFunctionIdentifiers fn = Except.ok () := by
  induction functions with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases hhead : validateFunctionIdentifiers head with
      | error err =>
          simp [validateFunctionIdentifierList, hhead] at hvalidate
          cases hvalidate
      | ok _ =>
          have htail : validateFunctionIdentifierList tail = Except.ok () := by
            simp only [validateFunctionIdentifierList, hhead] at hvalidate
            exact hvalidate
          simp at hmem
          rcases hmem with rfl | hmem
          · simp [hhead]
          · exact ih htail hmem

theorem validateFunctionIdentifiers_params_avoidReservedCompilerPrefix
    {fn : FunctionSpec}
    {name : String}
    (hvalidate : validateFunctionIdentifiers fn = Except.ok ())
    (hmem : name ∈ fn.params.map (·.name)) :
    ¬ name.startsWith "__" := by
  have hyul :
      validateFunctionYulIdentifiers fn = Except.ok () := by
    unfold validateFunctionIdentifiers at hvalidate
    cases hname : ensureContractIdentifier "function" fn.name with
    | error err =>
        simp [hname] at hvalidate
        cases hvalidate
    | ok _ =>
        simp only [hname] at hvalidate
        exact hvalidate
  exact validateFunctionYulIdentifiers_params_ok_of_mem hyul hmem

theorem validateFunctionIdentifiers_locals_avoidReservedCompilerPrefix
    {fn : FunctionSpec}
    {name : String}
    (hvalidate : validateFunctionIdentifiers fn = Except.ok ())
    (hmem : name ∈ collectStmtListBindNames fn.body) :
    ¬ name.startsWith "__" := by
  have hyul :
      validateFunctionYulIdentifiers fn = Except.ok () := by
    unfold validateFunctionIdentifiers at hvalidate
    cases hname : ensureContractIdentifier "function" fn.name with
    | error err =>
        simp [hname] at hvalidate
        cases hvalidate
    | ok _ =>
        simp only [hname] at hvalidate
        exact hvalidate
  exact validateFunctionYulIdentifiers_locals_ok_of_mem hyul hmem

theorem validateFunctionIdentifiers_assignTargets_avoidReservedCompilerPrefix
    {fn : FunctionSpec}
    {name : String}
    (hvalidate : validateFunctionIdentifiers fn = Except.ok ())
    (hmem : name ∈ collectStmtListAssignedNames fn.body) :
    ¬ name.startsWith "__" := by
  have hyul :
      validateFunctionYulIdentifiers fn = Except.ok () := by
    unfold validateFunctionIdentifiers at hvalidate
    cases hname : ensureContractIdentifier "function" fn.name with
    | error err =>
        simp [hname] at hvalidate
        cases hvalidate
    | ok _ =>
        simp only [hname] at hvalidate
        exact hvalidate
  exact validateFunctionYulIdentifiers_assignTargets_ok_of_mem hyul hmem

theorem validateIdentifierShapes_field_avoidReservedCompilerPrefix
    {spec : CompilationModel}
    {field : Field}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hmem : field ∈ spec.fields) :
    ¬ (field.name.startsWith "__" && !isInternalImmutableStorageName field.name) := by
  have hreserved :
      validateReservedCompilerIdentifiers spec = Except.ok () := by
    unfold validateIdentifierShapes at hvalidate
    cases hcontract : ensureContractIdentifier "contract" spec.name with
    | error err =>
        simp [hcontract] at hvalidate
        cases hvalidate
    | ok _ =>
        cases hreserved : validateReservedCompilerIdentifiers spec with
        | error err =>
            simp [hcontract, hreserved] at hvalidate
            cases hvalidate
        | ok a =>
            cases a
            rfl
  have hfields :
      validateFieldIdentifiers spec.fields = Except.ok () := by
    unfold validateReservedCompilerIdentifiers at hreserved
    cases hfields : validateFieldIdentifiers spec.fields with
    | error err =>
        simp [hfields] at hreserved
        cases hreserved
    | ok a =>
        cases a
        rfl
  exact validateFieldIdentifiers_ok_of_mem hfields hmem

theorem validateIdentifierShapes_functionIdentifiers_ok
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hmem : fn ∈ spec.functions) :
    validateFunctionIdentifiers fn = Except.ok () := by
  have hreserved :
      validateReservedCompilerIdentifiers spec = Except.ok () := by
    unfold validateIdentifierShapes at hvalidate
    cases hcontract : ensureContractIdentifier "contract" spec.name with
    | error err =>
        simp [hcontract] at hvalidate
        cases hvalidate
    | ok _ =>
        cases hreserved : validateReservedCompilerIdentifiers spec with
        | error err =>
            simp [hcontract, hreserved] at hvalidate
            cases hvalidate
        | ok a =>
            cases a
            rfl
  have hfunctions :
      validateFunctionIdentifierList spec.functions = Except.ok () := by
    unfold validateReservedCompilerIdentifiers at hreserved
    cases hfields : validateFieldIdentifiers spec.fields with
    | error err =>
        simp [hfields] at hreserved
        cases hreserved
    | ok _ =>
        cases hfunctions : validateFunctionIdentifierList spec.functions with
        | error err =>
            simp [hfields, hfunctions] at hreserved
            cases hreserved
        | ok a =>
            cases a
            rfl
  exact validateFunctionIdentifierList_ok_of_mem hfunctions hmem

theorem validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {name : String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hmem : name ∈ fn.params.map (·.name)) :
    ¬ name.startsWith "__" := by
  exact validateFunctionIdentifiers_params_avoidReservedCompilerPrefix
    (validateIdentifierShapes_functionIdentifiers_ok hvalidate hfn)
    hmem

theorem validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {name : String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hmem : name ∈ collectStmtListBindNames fn.body) :
    ¬ name.startsWith "__" := by
  exact validateFunctionIdentifiers_locals_avoidReservedCompilerPrefix
    (validateIdentifierShapes_functionIdentifiers_ok hvalidate hfn)
    hmem

theorem validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {name : String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hmem : name ∈ collectStmtListAssignedNames fn.body) :
    ¬ name.startsWith "__" := by
  exact validateFunctionIdentifiers_assignTargets_avoidReservedCompilerPrefix
    (validateIdentifierShapes_functionIdentifiers_ok hvalidate hfn)
    hmem

end Compiler.CompilationModel
