/-
  Compiler.CompilationModel.Validation: Validation walkers and shape checks
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.AbiTypeLayout
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.EcmAxiomCollection
import Compiler.CompilationModel.EventAbiHelpers
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.IssueRefs
import Compiler.CompilationModel.LayoutValidation
import Compiler.CompilationModel.LogicalPurity
import Compiler.CompilationModel.MappingWrites
import Compiler.CompilationModel.ScopeValidation
import Compiler.CompilationModel.TrustSurface
import Compiler.CompilationModel.UsageAnalysis
import Compiler.CompilationModel.ValidationCalls
import Compiler.CompilationModel.ValidationEvents
import Compiler.CompilationModel.ValidationHelpers
import Compiler.CompilationModel.ValidationInterop
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.CompilationModel.ExpressionCompile

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

private def firstDuplicateString : List String → Option String
  | [] => none
  | name :: rest =>
      if rest.contains name then some name else firstDuplicateString rest

private def missingDeclaredNames (actual declared : List String) : List String :=
  actual.foldl
    (fun acc name =>
      if declared.contains name || acc.contains name then acc else acc ++ [name])
    []

private def validateUnsafeYulDeclaredScopeEffects (fragment : UnsafeYulFragment) :
    Except String Unit := do
  let actual := yulStmtListScopeEffects fragment.stmts
  let missingBinds := missingDeclaredNames actual.bindNames fragment.scopeEffects.bindNames
  if !missingBinds.isEmpty then
    throw s!"Compilation error: unsafe Yul fragment '{fragment.label}' under-declares bound local(s): {String.intercalate ", " missingBinds}"
  let missingAssigns := missingDeclaredNames actual.assignNames fragment.scopeEffects.assignNames
  if !missingAssigns.isEmpty then
    throw s!"Compilation error: unsafe Yul fragment '{fragment.label}' under-declares assigned local(s): {String.intercalate ", " missingAssigns}"
  if !actual.storageWrites.isEmpty && fragment.scopeEffects.storageWrites.isEmpty then
    throw s!"Compilation error: unsafe Yul fragment '{fragment.label}' under-declares storage effects for raw Yul storage write(s)."

private def adtPayloadParamNames (params : List Param) : List String :=
  params.flatMap fun param =>
    match param.ty with
    | ParamType.adt _ maxFields =>
        (List.range maxFields).map fun idx => s!"{param.name}_f{idx}"
    | _ => []

private def validateAdtPayloadParamNameCollisions
    (context : String) (params : List Param) (body : List Stmt) : Except String Unit := do
  let generated := adtPayloadParamNames params
  match firstDuplicateString generated with
  | some name =>
      throw s!"Compilation error: {context} has ADT parameters whose generated payload local '{name}' collides. Rename the ADT parameters so generated '<param>_f<i>' locals are unique."
  | none => pure ()
  let userNames := params.map (·.name) ++ collectStmtListBindNames body
  match generated.find? (fun name => userNames.contains name) with
  | some name =>
      throw s!"Compilation error: {context} reserves generated ADT payload local '{name}'. Rename the parameter or local binding that conflicts with generated '<param>_f<i>' locals."
  | none => pure ()

private def immutableNames (immutables : List ImmutableSpec) : List String :=
  immutables.map (·.name)

private def validateModelImmutableExprNameNode (names : List String)
    (context : String) : Expr → Except String Unit
  | Expr.immutable name =>
      if names.contains name then
        pure ()
      else
        throw s!"Compilation error: {context} references unknown immutable '{name}'"
  | _ => pure ()

private def validateModelImmutableStmtNode (names : List String)
    (context : String) : Stmt → Except String Unit
  | stmt => do
      match stmt with
      | Stmt.setImmutable name _ =>
          if names.contains name then
            pure ()
          else
            throw s!"Compilation error: {context} sets unknown immutable '{name}'"
      | _ => pure ()
      for expr in stmt.directMetadata.subexpressions do
        expr.checkRec (validateModelImmutableExprNameNode names context)

private def validateSetImmutableRuntimeGuardNode (fnName : String) : Stmt → Except String Unit
  | Stmt.setImmutable name _ =>
      throw s!"Compilation error: function '{fnName}' uses Stmt.setImmutable for immutable '{name}' outside constructor scope"
  | _ => pure ()

def validateSetImmutableRuntimeGuard (fn : FunctionSpec) : Except String Unit :=
  Stmt.checkRecList (validateSetImmutableRuntimeGuardNode fn.name) fn.body

def validateImmutableNamesInFunction (immutables : List ImmutableSpec)
    (fn : FunctionSpec) : Except String Unit :=
  Stmt.checkRecList (validateModelImmutableStmtNode (immutableNames immutables) s!"function '{fn.name}'") fn.body

def validateImmutableNamesInConstructor (immutables : List ImmutableSpec)
    (ctor : Option ConstructorSpec) : Except String Unit := do
  let names := immutableNames immutables
  match ctor with
  | none => pure ()
  | some spec =>
      for imm in immutables do
        imm.init.checkRec (validateModelImmutableExprNameNode names s!"immutable '{imm.name}' initializer")
      Stmt.checkRecList (validateModelImmutableStmtNode names "constructor") spec.body

/-- Each declared immutable must be assigned via `Stmt.setImmutable` in the
    constructor body; deploy code only emits `setimmutable` from those
    statements (never from `ImmutableSpec.init`), so an unset immutable would
    read uninitialized bytecode at runtime. -/
def validateImmutableInitialization (immutables : List ImmutableSpec)
    (ctor : Option ConstructorSpec) : Except String Unit := do
  match immutables with
  | [] => pure ()
  | _ =>
      match ctor with
      | none =>
          throw "Compilation error: contract declares immutables but has no constructor to initialize them"
      | some spec =>
          for imm in immutables do
            let isSet := Stmt.foldBoolList
              (fun s => match s with
                | Stmt.setImmutable name _ => name == imm.name
                | _ => false) spec.body
            if isSet then
              pure ()
            else
              throw s!"Compilation error: immutable '{imm.name}' is declared but never initialized in the constructor"

def isStorageWordArrayParam : ParamType → Bool
  | ty => isWordArrayParam ty

/-- Node-local check for statement parameter references; nested statement
    bodies are reached via the canonical `Stmt.forDeepM`. -/
def validateStmtParamReferencesNode (fnName : String) (params : List Param) :
    Stmt → Except String Unit
  | Stmt.returnArray name =>
      match findParamType params name with
      | some ty =>
          if isWordArrayParam ty then
            pure ()
          else
            throw s!"Compilation error: function '{fnName}' returnArray '{name}' requires an array parameter with single-word static elements, got {repr ty}"
      | none =>
          pure ()
  | Stmt.returnBytes name =>
      match findParamType params name with
      | some ParamType.bytes | some ParamType.string => pure ()
      | some ty =>
          throw s!"Compilation error: function '{fnName}' returnBytes '{name}' requires bytes/string parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: function '{fnName}' returnBytes references unknown parameter '{name}'"
  | Stmt.returnStorageWords name =>
      match findParamType params name with
      | some ty =>
          if isStorageWordArrayParam ty then
            pure ()
          else
            throw s!"Compilation error: function '{fnName}' returnStorageWords '{name}' requires an array parameter with single-word static elements, got {repr ty}"
      | none =>
          throw s!"Compilation error: function '{fnName}' returnStorageWords references unknown parameter '{name}'"
  | Stmt.returnCodeData _pointer =>
      -- `returnCodeData` may return a pointer computed into a local; the scope-aware
      -- validator checks the expression once local bindings are available.
      pure ()
  | _ => pure ()

def validateStmtParamReferences (fnName : String) (params : List Param)
    (stmt : Stmt) : Except String Unit :=
  stmt.checkRec (validateStmtParamReferencesNode fnName params)

def validateStmtParamReferencesInList (fnName : String) (params : List Param)
    (stmts : List Stmt) : Except String Unit :=
  Stmt.checkRecList (validateStmtParamReferencesNode fnName params) stmts

def validateStmtParamReferencesInBranches (fnName : String) (params : List Param)
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  Stmt.checkRecBranches (validateStmtParamReferencesNode fnName params) branches

def validateStmtParamReferences_viaFold (fnName : String) (params : List Param)
    (stmt : Stmt) : Except String Unit :=
  Stmt.checkRec (validateStmtParamReferencesNode fnName params) stmt

def validateStmtParamReferencesInList_viaFold (fnName : String) (params : List Param)
    (stmts : List Stmt) : Except String Unit :=
  Stmt.checkRecList (validateStmtParamReferencesNode fnName params) stmts

def validateStmtParamReferencesInBranches_viaFold (fnName : String) (params : List Param)
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  Stmt.checkRecBranches (validateStmtParamReferencesNode fnName params) branches

theorem validateStmtParamReferences_eq_viaFold
    (fnName : String) (params : List Param) (stmt : Stmt) :
    validateStmtParamReferences fnName params stmt =
      validateStmtParamReferences_viaFold fnName params stmt := by
  rfl

theorem validateStmtParamReferencesInList_eq_viaFold
    (fnName : String) (params : List Param) (stmts : List Stmt) :
    validateStmtParamReferencesInList fnName params stmts =
      validateStmtParamReferencesInList_viaFold fnName params stmts := by
  rfl

theorem validateStmtParamReferencesInBranches_eq_viaFold
    (fnName : String) (params : List Param)
    (branches : List (String × List String × List Stmt)) :
    validateStmtParamReferencesInBranches fnName params branches =
      validateStmtParamReferencesInBranches_viaFold fnName params branches := by
  rfl

/-- Node-local return-shape check; nested statement bodies are reached via
    the canonical `Stmt.forDeepM`. -/
def validateReturnShapesNode (fnName : String) (params : List Param)
    (expectedReturns : List ParamType) (isInternal : Bool) : Stmt → Except String Unit
  | Stmt.return _ =>
      if isInternal then
        match expectedReturns with
        | [_] => pure ()
        | [] =>
            throw s!"Compilation error: function '{fnName}' uses Stmt.return but declares no return values"
        | _ =>
            throw s!"Compilation error: function '{fnName}' uses Stmt.return but declares multiple return values; use Stmt.returnValues"
      else if expectedReturns.length > 1 then
        throw s!"Compilation error: function '{fnName}' uses Stmt.return but declares multiple return values; use Stmt.returnValues"
      else
        pure ()
  | Stmt.returnValues values =>
      if expectedReturns.isEmpty then
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnValues but declares no return values"
      else if values.length != expectedReturns.length then
        throw s!"Compilation error: function '{fnName}' returnValues count mismatch: expected {expectedReturns.length}, got {values.length}"
      else
        pure ()
  | Stmt.returnArray name =>
      match findParamType params name with
      | some ty =>
          if !isWordArrayParam ty then
            throw s!"Compilation error: function '{fnName}' uses Stmt.returnArray with parameter '{name}' of type {repr ty}; only arrays with single-word static elements are currently supported"
          else if expectedReturns == [ty] then
            pure ()
          else
            throw s!"Compilation error: function '{fnName}' uses Stmt.returnArray to return parameter '{name}' of type {repr ty}, but declared returns are {repr expectedReturns}"
      | none =>
          match expectedReturns with
          | [ty] =>
              if isWordArrayParam ty then
                pure ()
              else
                throw s!"Compilation error: function '{fnName}' uses Stmt.returnArray with memory array '{name}', but declared return type {repr ty} is not a supported word array"
          | _ =>
              throw s!"Compilation error: function '{fnName}' returnArray references unknown parameter '{name}'"
  | Stmt.returnBytes name =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnBytes; only static returns via Stmt.return/Stmt.returnValues are supported ({issue625Ref})."
      else if expectedReturns == [ParamType.bytes] || expectedReturns == [ParamType.string] then
        match findParamType params name with
        | some ty =>
            if expectedReturns == [ty] then
              pure ()
            else
              throw s!"Compilation error: function '{fnName}' uses Stmt.returnBytes to return parameter '{name}' of type {repr ty}, but declared returns are {repr expectedReturns}"
        | none =>
            throw s!"Compilation error: function '{fnName}' returnBytes references unknown parameter '{name}'"
      else
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnBytes but declared returns are {repr expectedReturns}"
  | Stmt.returnStorageWords _ =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnStorageWords; only static returns via Stmt.return/Stmt.returnValues are supported ({issue625Ref})."
      else if expectedReturns == [ParamType.array ParamType.uint256] then
        pure ()
      else
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnStorageWords but declared returns are {repr expectedReturns}"
  | Stmt.returnCodeData _ =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnCodeData; only static returns via Stmt.return/Stmt.returnValues are supported ({issue625Ref})."
      else if expectedReturns.isEmpty then
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnCodeData but declares no return values"
      else
        -- #1982: CodeData (SSTORE2-style) returns remain static-only for now.
        -- Full lifting of the static gate (dynamic payloads, broader return shapes)
        -- is tracked under the 1982 dynamic/composite ABI work.
        pure ()
  | _ => pure ()

def validateReturnShapesInStmt (fnName : String) (params : List Param)
    (expectedReturns : List ParamType) (isInternal : Bool) (stmt : Stmt) :
    Except String Unit :=
  stmt.checkRec (validateReturnShapesNode fnName params expectedReturns isInternal)

def validateReturnShapesInStmtList (fnName : String)
    (params : List Param) (expectedReturns : List ParamType) (isInternal : Bool)
    (stmts : List Stmt) : Except String Unit :=
  Stmt.checkRecList (validateReturnShapesNode fnName params expectedReturns isInternal) stmts

def validateReturnShapesInBranches (fnName : String)
    (params : List Param) (expectedReturns : List ParamType) (isInternal : Bool)
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  Stmt.checkRecBranches
    (validateReturnShapesNode fnName params expectedReturns isInternal) branches

def validateReturnShapesInStmt_viaFold (fnName : String) (params : List Param)
    (expectedReturns : List ParamType) (isInternal : Bool) (stmt : Stmt) :
    Except String Unit :=
  Stmt.checkRec (validateReturnShapesNode fnName params expectedReturns isInternal) stmt

def validateReturnShapesInStmtList_viaFold (fnName : String)
    (params : List Param) (expectedReturns : List ParamType) (isInternal : Bool)
    (stmts : List Stmt) : Except String Unit :=
  Stmt.checkRecList (validateReturnShapesNode fnName params expectedReturns isInternal) stmts

def validateReturnShapesInBranches_viaFold (fnName : String)
    (params : List Param) (expectedReturns : List ParamType) (isInternal : Bool)
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  Stmt.checkRecBranches
    (validateReturnShapesNode fnName params expectedReturns isInternal) branches

theorem validateReturnShapesInStmt_eq_viaFold
    (fnName : String) (params : List Param) (expectedReturns : List ParamType)
    (isInternal : Bool) (stmt : Stmt) :
    validateReturnShapesInStmt fnName params expectedReturns isInternal stmt =
      validateReturnShapesInStmt_viaFold fnName params expectedReturns isInternal stmt := by
  rfl

theorem validateReturnShapesInStmtList_eq_viaFold
    (fnName : String) (params : List Param) (expectedReturns : List ParamType)
    (isInternal : Bool) (stmts : List Stmt) :
    validateReturnShapesInStmtList fnName params expectedReturns isInternal stmts =
      validateReturnShapesInStmtList_viaFold fnName params expectedReturns isInternal stmts := by
  rfl

theorem validateReturnShapesInBranches_eq_viaFold
    (fnName : String) (params : List Param) (expectedReturns : List ParamType)
    (isInternal : Bool) (branches : List (String × List String × List Stmt)) :
    validateReturnShapesInBranches fnName params expectedReturns isInternal branches =
      validateReturnShapesInBranches_viaFold
        fnName params expectedReturns isInternal branches := by
  rfl

private def stmtListAlwaysReturnsOrReverts (stmts : List Stmt) : Bool :=
  ControlFlowSummary.alwaysReturnsOrReverts (Stmt.controlFlowList stmts)

/-- Node-local classifier: does this expression itself read state or the
    environment? `externalCall` to the builtin exponentiation helper is pure.
    Lifted with the canonical `Expr.anyDeep`. -/
def exprReadsStateOrEnvNode : Expr → Bool
  | Expr.storage _ | Expr.storageAddr _
  | Expr.mapping _ _ | Expr.mappingWord _ _ _ | Expr.mappingPackedWord _ _ _ _
  | Expr.mapping2 _ _ _ | Expr.mapping2Word _ _ _ _
  | Expr.mappingUint _ _ | Expr.mappingChain _ _
  | Expr.structMember _ _ _ | Expr.structMember2 _ _ _ _
  | Expr.caller | Expr.contractAddress | Expr.txOrigin | Expr.chainid
  | Expr.extcodesize _ | Expr.msgValue | Expr.selfBalance
  | Expr.blockTimestamp | Expr.blockNumber | Expr.blobbasefee
  | Expr.calldatasize | Expr.calldataload _ | Expr.tload _
  | Expr.call _ _ _ _ _ _ _ | Expr.staticcall _ _ _ _ _ _
  | Expr.delegatecall _ _ _ _ _ _
  | Expr.returndataSize | Expr.returndataOptionalBoolAt _
  | Expr.internalCall _ _
  | Expr.storageArrayLength _ | Expr.storageArrayElement _ _
  | Expr.adtTag _ _ | Expr.adtField _ _ _ _ _ => true
  | Expr.externalCall name _ => name != builtinExpName
  | _ => false

def exprReadsStateOrEnv (e : Expr) : Bool :=
  e.anyDeep exprReadsStateOrEnvNode

/-- Node-local classifier: does this expression itself write state? Lifted
    with the canonical `Expr.anyDeep` (so `staticcall` operands etc. are still
    scanned, exactly like the old walk). -/
def exprWritesStateNode : Expr → Bool
  | Expr.call _ _ _ _ _ _ _ | Expr.delegatecall _ _ _ _ _ _ => true
  | Expr.externalCall name _ => name != builtinExpName
  | Expr.internalCall _ _ => true
  | _ => false

def exprWritesState (e : Expr) : Bool :=
  e.anyDeep exprWritesStateNode

def exprListWritesState (es : List Expr) : Bool :=
  es.any exprWritesState

/-- Node-local statement classifier for state writes; nested statement bodies
    are reached via the canonical `Stmt.anyDeep`. -/
def stmtWritesStateNode : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value =>
      exprWritesState value
  | Stmt.setStorage _ _ | Stmt.setStorageAddr _ _ | Stmt.setStorageWord _ _ _
  | Stmt.storageArrayPush _ _ | Stmt.storageArrayPop _ | Stmt.setStorageArrayElement _ _ _
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMappingChain _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _ => true
  | Stmt.require cond _ =>
      exprWritesState cond
  | Stmt.requireError cond _ args =>
      exprWritesState cond || exprListWritesState args
  | Stmt.revertError _ args =>
      exprListWritesState args
  | Stmt.return value =>
      exprWritesState value
  | Stmt.returnValues values =>
      exprListWritesState values
  | Stmt.returnCodeData pointer =>
      exprWritesState pointer
  | Stmt.unsafeYul fragment =>
      !fragment.scopeEffects.storageWrites.isEmpty || fragment.mechanics.contains .tstore
  | Stmt.mstore offset value =>
      exprWritesState offset || exprWritesState value
  | Stmt.tstore _ _ =>
      true
  | Stmt.calldatacopy destOffset sourceOffset size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprWritesState destOffset || exprWritesState sourceOffset || exprWritesState size
  | Stmt.ite cond _ _ =>
      exprWritesState cond
  | Stmt.forEach _ count _ | Stmt.forEachSetBit _ count _ =>
      exprWritesState count
  | Stmt.emit _ _ | Stmt.rawLog _ _ _
  | Stmt.internalCall _ _ | Stmt.internalCallAssign _ _ _
  | Stmt.externalCallBind _ _ _ | Stmt.tryExternalCallBind _ _ _ _ => true
  | Stmt.ecm mod args =>
      mod.writesState || exprListWritesState args
  | Stmt.matchAdt _ scrutinee _ =>
      exprWritesState scrutinee
  | _ => false

def stmtWritesState (s : Stmt) : Bool :=
  s.anyDeep stmtWritesStateNode

def stmtListWritesState (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList stmtWritesStateNode stmts

def matchBranchesWriteState (branches : List (String × List String × List Stmt)) : Bool :=
  branches.any fun (_, _, body) => stmtListWritesState body

/-- Collect the set of storage field names written by a statement.
    The per-statement contribution is exactly the canonical
    `directMetadata.scopeEffects.storageWrites` (which also covers raw
    `unsafeYul` fragments); nested statement bodies are reached via
    `Stmt.childLists`. Used by `modifies(...)` validation (#1729, Axis 3 Step 1b). -/
def stmtWrittenFields (s : Stmt) : List String :=
  s.directMetadata.scopeEffects.storageWrites ++
    (Stmt.childLists s).attach.flatMap (fun ⟨l, hl⟩ =>
      l.attach.flatMap (fun ⟨c, hc⟩ =>
        have := Stmt.childLists_sizeOf_lt s l hl c hc
        stmtWrittenFields c))
termination_by sizeOf s
decreasing_by exact Nat.lt_trans this.1 this.2

def stmtListWrittenFields (stmts : List Stmt) : List String :=
  stmts.flatMap stmtWrittenFields

def matchBranchesWrittenFields (branches : List (String × List String × List Stmt)) : List String :=
  branches.flatMap fun (_, _, body) => stmtListWrittenFields body

/-- Detect expression-position internal helper calls whose callee write set is
    not visible to single-function `modifies(...)` validation. External-call
    forms (`externalCall`/`call`/`staticcall`/`delegatecall`) deliberately do
    NOT recurse into their operands, exactly like the old walk; all other
    constructors recurse via the canonical `Expr.children`. -/
def exprHasUntrackableWrites : Expr → Bool
  | Expr.internalCall _ _ => true
  | Expr.externalCall _ _ | Expr.call _ _ _ _ _ _ _
  | Expr.staticcall _ _ _ _ _ _ | Expr.delegatecall _ _ _ _ _ _ => false
  | e =>
      (Expr.children e).attach.any (fun ⟨c, hc⟩ =>
        have := Expr.children_sizeOf_lt e c hc
        exprHasUntrackableWrites c)
termination_by e => sizeOf e

def exprListHasUntrackableWrites (es : List Expr) : Bool :=
  es.any exprHasUntrackableWrites

/-- Node-local statement classifier for untrackable writes; nested statement
    bodies are reached via the canonical `Stmt.anyDeep`. External calls
    (`externalCallBind`, `tryExternalCallBind`, `ecm`) target other contracts
    and cannot directly modify the current contract's storage fields, so they
    are safe for `modifies()` (as in the old walk). -/
def stmtHasUntrackableWritesNode : Stmt → Bool
  | Stmt.internalCall _ _ | Stmt.internalCallAssign _ _ _ => true
  | Stmt.letVar _ value | Stmt.assignVar _ value =>
      exprHasUntrackableWrites value
  | Stmt.setStorage _ value | Stmt.setStorageAddr _ value
  | Stmt.require value _ =>
      exprHasUntrackableWrites value
  | Stmt.setStorageWord _ wordOffset value =>
      -- Nonzero wordOffset writes to a sibling field that `stmtWrittenFields`
      -- cannot track (it returns only the base field), so flag as untrackable
      -- to keep `modifies(...)` validation sound.
      wordOffset != 0 || exprHasUntrackableWrites value
  | Stmt.requireError cond _ args =>
      exprHasUntrackableWrites cond || args.any exprHasUntrackableWrites
  | Stmt.revertError _ args | Stmt.returnValues args | Stmt.emit _ args =>
      args.any exprHasUntrackableWrites
  | Stmt.return value | Stmt.storageArrayPush _ value =>
      exprHasUntrackableWrites value
  | Stmt.setStorageArrayElement _ index value =>
      exprHasUntrackableWrites index || exprHasUntrackableWrites value
  | Stmt.setMapping _ key value | Stmt.setMappingUint _ key value =>
      exprHasUntrackableWrites key || exprHasUntrackableWrites value
  | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value =>
      exprHasUntrackableWrites key || exprHasUntrackableWrites value
  | Stmt.setMappingChain _ keys value =>
      keys.any exprHasUntrackableWrites || exprHasUntrackableWrites value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value =>
      exprHasUntrackableWrites key1 || exprHasUntrackableWrites key2 || exprHasUntrackableWrites value
  | Stmt.setStructMember _ key _ value =>
      exprHasUntrackableWrites key || exprHasUntrackableWrites value
  | Stmt.rawLog topics dataOffset dataSize =>
      topics.any exprHasUntrackableWrites || exprHasUntrackableWrites dataOffset || exprHasUntrackableWrites dataSize
  | Stmt.mstore offset value | Stmt.tstore offset value =>
      exprHasUntrackableWrites offset || exprHasUntrackableWrites value
  | Stmt.calldatacopy destOffset sourceOffset size | Stmt.returndataCopy destOffset sourceOffset size =>
      exprHasUntrackableWrites destOffset || exprHasUntrackableWrites sourceOffset || exprHasUntrackableWrites size
  | Stmt.ite cond _ _ =>
      exprHasUntrackableWrites cond
  | Stmt.forEach _ count _ | Stmt.forEachSetBit _ count _ =>
      exprHasUntrackableWrites count
  | Stmt.unsafeYul fragment =>
      -- Raw Yul storage writes target computed slots that cannot be tied back to
      -- declared storage fields, so any storage-writing fragment is untrackable.
      !fragment.scopeEffects.storageWrites.isEmpty || fragment.mechanics.contains .storageWrite
  | Stmt.matchAdt _ scrutinee _ =>
      exprHasUntrackableWrites scrutinee
  | _ => false

/-- Check whether a statement may write to storage fields that `stmtWrittenFields`
    cannot track. Used by `modifies(...)` validation to conservatively reject
    annotations when write-set tracking is incomplete. -/
def stmtHasUntrackableWrites (s : Stmt) : Bool :=
  s.anyDeep stmtHasUntrackableWritesNode

def stmtListHasUntrackableWrites (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList stmtHasUntrackableWritesNode stmts

def matchBranchesHasUntrackableWrites (branches : List (String × List String × List Stmt)) : Bool :=
  branches.any fun (_, _, body) => stmtListHasUntrackableWrites body

/-- Node-local classifier: is this expression itself an external call (call,
    staticcall, delegatecall, or non-builtin externalCall)? Lifted with the
    canonical `Expr.anyDeep`. Used by `no_external_calls` validation
    (#1729, Axis 3 Step 1c). -/
def exprContainsExternalCallNode : Expr → Bool
  | Expr.call _ _ _ _ _ _ _ | Expr.staticcall _ _ _ _ _ _
  | Expr.delegatecall _ _ _ _ _ _ => true
  | Expr.externalCall name _ => name != builtinExpName
  | _ => false

def exprContainsExternalCall (e : Expr) : Bool :=
  e.anyDeep exprContainsExternalCallNode

def exprListContainsExternalCall (es : List Expr) : Bool :=
  es.any exprContainsExternalCall

/-- Conservative variant of `exprContainsExternalCallNode` for annotations such
    as `no_external_calls`, where an internal helper expression may itself
    perform an external interaction. CEI uses `exprContainsExternalCall`
    instead so that local helper reads do not become false interaction
    barriers. -/
def exprMayContainExternalCallNode : Expr → Bool
  | Expr.internalCall _ _ => true
  | e => exprContainsExternalCallNode e

def exprMayContainExternalCall (e : Expr) : Bool :=
  e.anyDeep exprMayContainExternalCallNode

def exprListMayContainExternalCall (es : List Expr) : Bool :=
  es.any exprMayContainExternalCall

/-- Node-local statement classifier for external calls; nested statement
    bodies are reached via the canonical `Stmt.anyDeep`.
    Used by `no_external_calls` validation (#1729, Axis 3 Step 1c). -/
def stmtContainsExternalCallNode : Stmt → Bool
  | Stmt.externalCallBind _ _ _ | Stmt.tryExternalCallBind _ _ _ _ => true
  | Stmt.ecm _ _ => true
  | Stmt.letVar _ value | Stmt.assignVar _ value =>
      exprContainsExternalCall value
  | Stmt.setStorage _ value | Stmt.setStorageAddr _ value | Stmt.setStorageWord _ _ value
  | Stmt.require value _ =>
      exprContainsExternalCall value
  | Stmt.requireError cond _ args =>
      exprContainsExternalCall cond || args.any exprContainsExternalCall
  | Stmt.revertError _ args =>
      args.any exprContainsExternalCall
  | Stmt.return value =>
      exprContainsExternalCall value
  | Stmt.returnValues values =>
      values.any exprContainsExternalCall
  | Stmt.storageArrayPush _ value =>
      exprContainsExternalCall value
  | Stmt.setStorageArrayElement _ index value =>
      exprContainsExternalCall index || exprContainsExternalCall value
  | Stmt.setMapping _ key value | Stmt.setMappingUint _ key value =>
      exprContainsExternalCall key || exprContainsExternalCall value
  | Stmt.setMappingWord _ key _ value =>
      exprContainsExternalCall key || exprContainsExternalCall value
  | Stmt.setMappingPackedWord _ key _ _ value =>
      exprContainsExternalCall key || exprContainsExternalCall value
  | Stmt.setMappingChain _ keys value =>
      keys.any exprContainsExternalCall || exprContainsExternalCall value
  | Stmt.setMapping2 _ key1 key2 value =>
      exprContainsExternalCall key1 || exprContainsExternalCall key2 || exprContainsExternalCall value
  | Stmt.setMapping2Word _ key1 key2 _ value =>
      exprContainsExternalCall key1 || exprContainsExternalCall key2 || exprContainsExternalCall value
  | Stmt.setStructMember _ key _ value =>
      exprContainsExternalCall key || exprContainsExternalCall value
  | Stmt.setStructMember2 _ key1 key2 _ value =>
      exprContainsExternalCall key1 || exprContainsExternalCall key2 || exprContainsExternalCall value
  | Stmt.emit _ args =>
      args.any exprContainsExternalCall
  | Stmt.rawLog topics dataOffset dataSize =>
      topics.any exprContainsExternalCall || exprContainsExternalCall dataOffset || exprContainsExternalCall dataSize
  | Stmt.tstore offset value | Stmt.mstore offset value =>
      exprContainsExternalCall offset || exprContainsExternalCall value
  | Stmt.calldatacopy destOffset sourceOffset size =>
      exprContainsExternalCall destOffset || exprContainsExternalCall sourceOffset || exprContainsExternalCall size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprContainsExternalCall destOffset || exprContainsExternalCall sourceOffset || exprContainsExternalCall size
  | Stmt.ite cond _ _ =>
      exprContainsExternalCall cond
  | Stmt.forEach _ count _ | Stmt.forEachSetBit _ count _ =>
      exprContainsExternalCall count
  | Stmt.matchAdt _ scrutinee _ =>
      exprContainsExternalCall scrutinee
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args =>
      args.any exprContainsExternalCall
  | Stmt.unsafeYul fragment =>
      fragment.mechanics.contains .call ||
        fragment.mechanics.contains .staticcall ||
        fragment.mechanics.contains .delegatecall ||
        yulStmtListContainsExternalCall fragment.stmts
  | _ => false

def stmtContainsExternalCall (s : Stmt) : Bool :=
  s.anyDeep stmtContainsExternalCallNode

def stmtListContainsExternalCall (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList stmtContainsExternalCallNode stmts

def matchBranchesContainExternalCall (branches : List (String × List String × List Stmt)) : Bool :=
  branches.any fun (_, _, body) => stmtListContainsExternalCall body

/-- Node-local classifier for the cross-function reentrancy gate: which
    statements hand control to untrusted code in a way that can corrupt this
    contract's state via a reentrant entrypoint. It mirrors
    `stmtContainsExternalCallNode` but refines the `ecm` arm: an External Call
    Module summarised as a `staticcall` (precompiles, `keccak`/`sha256`, ABI
    encoding, view-only reads) runs in the EVM static context, where any
    state-mutating opcode reverts — such a call provably cannot open a
    state-corrupting reentrancy window, so it does not require a disposition.
    Every other external-call form (a mutating `call` ECM, a `externalCall`
    binding, a non-builtin `externalCall` expression, raw-Yul `call`/`staticcall`/
    `delegatecall`) stays window-opening: it reaches an external contract that
    may re-enter. -/
def stmtReentrancyWindowNode : Stmt → Bool
  | Stmt.ecm mod _ =>
      mod.summaryMutability == Compiler.ECM.StatefulExternal.Mutability.call
  | s => stmtContainsExternalCallNode s

/-- Whether a statement (deeply) opens a cross-function reentrancy window. -/
def stmtOpensReentrancyWindow (s : Stmt) : Bool :=
  s.anyDeep stmtReentrancyWindowNode

/-- Conservative variant of `stmtContainsExternalCallNode` for
    `no_external_calls` validation. Returns `true` for internal calls because
    callee bodies may contain external calls that are not visible at
    single-function validation scope. -/
def stmtMayContainExternalCallNode : Stmt → Bool
  | Stmt.internalCall _ _ | Stmt.internalCallAssign _ _ _ => true
  | Stmt.ite cond _ _ =>
      exprMayContainExternalCall cond
  | Stmt.forEach _ count _ | Stmt.forEachSetBit _ count _ =>
      exprMayContainExternalCall count
  | Stmt.matchAdt _ scrutinee _ =>
      exprMayContainExternalCall scrutinee
  | Stmt.letVar _ value | Stmt.assignVar _ value =>
      exprMayContainExternalCall value
  | Stmt.setStorage _ value | Stmt.setStorageAddr _ value | Stmt.setStorageWord _ _ value
  | Stmt.require value _ =>
      exprMayContainExternalCall value
  | Stmt.requireError cond _ args =>
      exprMayContainExternalCall cond || args.any exprMayContainExternalCall
  | Stmt.revertError _ args =>
      args.any exprMayContainExternalCall
  | Stmt.return value =>
      exprMayContainExternalCall value
  | Stmt.returnValues values =>
      values.any exprMayContainExternalCall
  | Stmt.storageArrayPush _ value =>
      exprMayContainExternalCall value
  | Stmt.setStorageArrayElement _ index value =>
      exprMayContainExternalCall index || exprMayContainExternalCall value
  | Stmt.setMapping _ key value | Stmt.setMappingUint _ key value =>
      exprMayContainExternalCall key || exprMayContainExternalCall value
  | Stmt.setMappingWord _ key _ value =>
      exprMayContainExternalCall key || exprMayContainExternalCall value
  | Stmt.setMappingPackedWord _ key _ _ value =>
      exprMayContainExternalCall key || exprMayContainExternalCall value
  | Stmt.setMappingChain _ keys value =>
      keys.any exprMayContainExternalCall || exprMayContainExternalCall value
  | Stmt.setMapping2 _ key1 key2 value =>
      exprMayContainExternalCall key1 || exprMayContainExternalCall key2 || exprMayContainExternalCall value
  | Stmt.setMapping2Word _ key1 key2 _ value =>
      exprMayContainExternalCall key1 || exprMayContainExternalCall key2 || exprMayContainExternalCall value
  | Stmt.setStructMember _ key _ value =>
      exprMayContainExternalCall key || exprMayContainExternalCall value
  | Stmt.setStructMember2 _ key1 key2 _ value =>
      exprMayContainExternalCall key1 || exprMayContainExternalCall key2 || exprMayContainExternalCall value
  | Stmt.emit _ args =>
      args.any exprMayContainExternalCall
  | Stmt.rawLog topics dataOffset dataSize =>
      topics.any exprMayContainExternalCall || exprMayContainExternalCall dataOffset || exprMayContainExternalCall dataSize
  | Stmt.tstore offset value | Stmt.mstore offset value =>
      exprMayContainExternalCall offset || exprMayContainExternalCall value
  | Stmt.calldatacopy destOffset sourceOffset size =>
      exprMayContainExternalCall destOffset || exprMayContainExternalCall sourceOffset || exprMayContainExternalCall size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprMayContainExternalCall destOffset || exprMayContainExternalCall sourceOffset || exprMayContainExternalCall size
  | s => stmtContainsExternalCallNode s

def stmtMayContainExternalCall (s : Stmt) : Bool :=
  s.anyDeep stmtMayContainExternalCallNode

def stmtListMayContainExternalCall (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList stmtMayContainExternalCallNode stmts

def matchBranchesMayContainExternalCall (branches : List (String × List String × List Stmt)) : Bool :=
  branches.any fun (_, _, body) => stmtListMayContainExternalCall body

/-- Node-local statement classifier for state/environment reads; nested
    statement bodies are reached via the canonical `Stmt.anyDeep`. -/
def stmtReadsStateOrEnvNode : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value
  | Stmt.setImmutable _ value | Stmt.setStorageWord _ _ value |
    Stmt.return value | Stmt.require value _ =>
      exprReadsStateOrEnv value
  | Stmt.storageArrayPush _ _ | Stmt.setStorageArrayElement _ _ _ | Stmt.storageArrayPop _ =>
      true
  | Stmt.requireError cond _ args =>
      exprReadsStateOrEnv cond || args.any exprReadsStateOrEnv
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      args.any exprReadsStateOrEnv
  | Stmt.returnArray _ | Stmt.returnBytes _ =>
      false
  | Stmt.returnStorageWords _ =>
      true
  | Stmt.returnCodeData _ =>
      true
  | Stmt.mstore offset value | Stmt.tstore offset value =>
      exprReadsStateOrEnv offset || exprReadsStateOrEnv value
  | Stmt.calldatacopy _ _ _ | Stmt.returndataCopy _ _ _ => true
  | Stmt.revertReturndata =>
      true
  | Stmt.stop =>
      false
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMappingChain _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _ => true
  | Stmt.ite cond _ _ =>
      exprReadsStateOrEnv cond
  | Stmt.forEach _ count _ | Stmt.forEachSetBit _ count _ =>
      exprReadsStateOrEnv count
  | Stmt.unsafeBlock _ _ =>
      false
  | Stmt.rawLog topics dataOffset dataSize =>
      topics.any exprReadsStateOrEnv || exprReadsStateOrEnv dataOffset || exprReadsStateOrEnv dataSize
  | Stmt.internalCall _ _ | Stmt.internalCallAssign _ _ _
  | Stmt.externalCallBind _ _ _ | Stmt.tryExternalCallBind _ _ _ _ => true
  | Stmt.ecm mod args => mod.readsState || mod.writesState || args.any exprReadsStateOrEnv
  | Stmt.matchAdt _ scrutinee _ =>
      exprReadsStateOrEnv scrutinee
  | Stmt.unsafeYul fragment =>
      !fragment.mechanics.isEmpty || !fragment.scopeEffects.storageWrites.isEmpty

def stmtReadsStateOrEnv (s : Stmt) : Bool :=
  s.anyDeep stmtReadsStateOrEnvNode

def stmtListReadsStateOrEnv (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList stmtReadsStateOrEnvNode stmts

def matchBranchesReadStateOrEnv (branches : List (String × List String × List Stmt)) : Bool :=
  branches.any fun (_, _, body) => stmtListReadsStateOrEnv body

structure FunctionEffect where
  writesState : Bool := false
  readsStateOrEnv : Bool := false
deriving BEq, Repr

private def unknownFunctionEffect : FunctionEffect :=
  { writesState := true, readsStateOrEnv := true }

private def lookupFunctionEffect
    (effects : List (String × FunctionEffect)) (name : String) : FunctionEffect :=
  match effects.find? (fun entry => entry.fst == name) with
  | some (_, effect) => effect
  | none => unknownFunctionEffect

/-- Node-local classifier for state writes with inferred per-function
    effects; lifted with the canonical `Expr.anyDeep`. -/
def exprWritesStateWithFunctionEffectsNode
    (effects : List (String × FunctionEffect)) : Expr → Bool
  | Expr.call _ _ _ _ _ _ _ | Expr.delegatecall _ _ _ _ _ _ => true
  | Expr.externalCall name _ => name != builtinExpName
  | Expr.internalCall name _ => (lookupFunctionEffect effects name).writesState
  | _ => false

def exprWritesStateWithFunctionEffects
    (effects : List (String × FunctionEffect)) (e : Expr) : Bool :=
  e.anyDeep (exprWritesStateWithFunctionEffectsNode effects)

def exprListWritesStateWithFunctionEffects
    (effects : List (String × FunctionEffect)) (es : List Expr) : Bool :=
  es.any (exprWritesStateWithFunctionEffects effects)

/-- Node-local statement classifier for state writes with inferred
    per-function effects; nested bodies via the canonical `Stmt.anyDeep`. -/
def stmtWritesStateWithFunctionEffectsNode
    (effects : List (String × FunctionEffect)) : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value =>
      exprWritesStateWithFunctionEffects effects value
  | Stmt.setStorage _ _ | Stmt.setStorageAddr _ _ | Stmt.setStorageWord _ _ _
  | Stmt.storageArrayPush _ _ | Stmt.storageArrayPop _ | Stmt.setStorageArrayElement _ _ _
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMappingChain _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _ => true
  | Stmt.require cond _ =>
      exprWritesStateWithFunctionEffects effects cond
  | Stmt.requireError cond _ args =>
      exprWritesStateWithFunctionEffects effects cond ||
        exprListWritesStateWithFunctionEffects effects args
  | Stmt.revertError _ args =>
      exprListWritesStateWithFunctionEffects effects args
  | Stmt.return value =>
      exprWritesStateWithFunctionEffects effects value
  | Stmt.returnValues values =>
      exprListWritesStateWithFunctionEffects effects values
  | Stmt.returnCodeData pointer =>
      exprWritesStateWithFunctionEffects effects pointer
  | Stmt.mstore offset value =>
      exprWritesStateWithFunctionEffects effects offset ||
        exprWritesStateWithFunctionEffects effects value
  | Stmt.tstore _ _ =>
      true
  | Stmt.calldatacopy destOffset sourceOffset size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprWritesStateWithFunctionEffects effects destOffset ||
        exprWritesStateWithFunctionEffects effects sourceOffset ||
        exprWritesStateWithFunctionEffects effects size
  | Stmt.ite cond _ _ =>
      exprWritesStateWithFunctionEffects effects cond
  | Stmt.forEach _ count _ | Stmt.forEachSetBit _ count _ =>
      exprWritesStateWithFunctionEffects effects count
  | Stmt.emit _ _ | Stmt.rawLog _ _ _
  | Stmt.externalCallBind _ _ _ | Stmt.tryExternalCallBind _ _ _ _ => true
  | Stmt.internalCall name args | Stmt.internalCallAssign _ name args =>
      (lookupFunctionEffect effects name).writesState ||
        exprListWritesStateWithFunctionEffects effects args
  | Stmt.ecm mod args =>
      mod.writesState || exprListWritesStateWithFunctionEffects effects args
  | Stmt.matchAdt _ scrutinee _ =>
      exprWritesStateWithFunctionEffects effects scrutinee
  | Stmt.unsafeYul fragment =>
      !fragment.scopeEffects.storageWrites.isEmpty || fragment.mechanics.contains .tstore
  | _ => false

def stmtWritesStateWithFunctionEffects
    (effects : List (String × FunctionEffect)) (s : Stmt) : Bool :=
  s.anyDeep (stmtWritesStateWithFunctionEffectsNode effects)

def stmtListWritesStateWithFunctionEffects
    (effects : List (String × FunctionEffect)) (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList (stmtWritesStateWithFunctionEffectsNode effects) stmts

def matchBranchesWriteStateWithFunctionEffects
    (effects : List (String × FunctionEffect))
    (branches : List (String × List String × List Stmt)) : Bool :=
  branches.any fun (_, _, body) => stmtListWritesStateWithFunctionEffects effects body

/-- Node-local classifier for state/environment reads with inferred
    per-function effects; lifted with the canonical `Expr.anyDeep`. -/
def exprReadsStateOrEnvWithFunctionEffectsNode
    (effects : List (String × FunctionEffect)) : Expr → Bool
  | Expr.internalCall name _ => (lookupFunctionEffect effects name).readsStateOrEnv
  | e => exprReadsStateOrEnvNode e

def exprReadsStateOrEnvWithFunctionEffects
    (effects : List (String × FunctionEffect)) (e : Expr) : Bool :=
  e.anyDeep (exprReadsStateOrEnvWithFunctionEffectsNode effects)

def exprListReadsStateOrEnvWithFunctionEffects
    (effects : List (String × FunctionEffect)) (es : List Expr) : Bool :=
  es.any (exprReadsStateOrEnvWithFunctionEffects effects)

/-- Node-local statement classifier for state/environment reads with inferred
    per-function effects; nested bodies via the canonical `Stmt.anyDeep`. -/
def stmtReadsStateOrEnvWithFunctionEffectsNode
    (effects : List (String × FunctionEffect)) : Stmt → Bool
  | Stmt.internalCall name args | Stmt.internalCallAssign _ name args =>
      (lookupFunctionEffect effects name).readsStateOrEnv ||
        exprListReadsStateOrEnvWithFunctionEffects effects args
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value
  | Stmt.setImmutable _ value | Stmt.setStorageWord _ _ value |
    Stmt.return value | Stmt.require value _ =>
      exprReadsStateOrEnvWithFunctionEffects effects value
  | Stmt.storageArrayPush _ _ | Stmt.setStorageArrayElement _ _ _ | Stmt.storageArrayPop _ =>
      true
  | Stmt.requireError cond _ args =>
      exprReadsStateOrEnvWithFunctionEffects effects cond ||
        exprListReadsStateOrEnvWithFunctionEffects effects args
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      exprListReadsStateOrEnvWithFunctionEffects effects args
  | Stmt.returnArray _ | Stmt.returnBytes _ =>
      false
  | Stmt.returnStorageWords _ =>
      true
  | Stmt.returnCodeData _ =>
      true
  | Stmt.mstore offset value | Stmt.tstore offset value =>
      exprReadsStateOrEnvWithFunctionEffects effects offset ||
        exprReadsStateOrEnvWithFunctionEffects effects value
  | Stmt.calldatacopy _ _ _ | Stmt.returndataCopy _ _ _ => true
  | Stmt.revertReturndata =>
      true
  | Stmt.stop =>
      false
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMappingChain _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _ => true
  | Stmt.ite cond _ _ =>
      exprReadsStateOrEnvWithFunctionEffects effects cond
  | Stmt.forEach _ count _ | Stmt.forEachSetBit _ count _ =>
      exprReadsStateOrEnvWithFunctionEffects effects count
  | Stmt.unsafeBlock _ _ =>
      false
  | Stmt.rawLog topics dataOffset dataSize =>
      topics.any (exprReadsStateOrEnvWithFunctionEffects effects) ||
        exprReadsStateOrEnvWithFunctionEffects effects dataOffset ||
        exprReadsStateOrEnvWithFunctionEffects effects dataSize
  | Stmt.externalCallBind _ _ _ | Stmt.tryExternalCallBind _ _ _ _ => true
  | Stmt.ecm mod args =>
      mod.readsState || mod.writesState ||
        exprListReadsStateOrEnvWithFunctionEffects effects args
  | Stmt.matchAdt _ scrutinee _ =>
      exprReadsStateOrEnvWithFunctionEffects effects scrutinee
  | Stmt.unsafeYul fragment =>
      !fragment.mechanics.isEmpty || !fragment.scopeEffects.storageWrites.isEmpty

def stmtReadsStateOrEnvWithFunctionEffects
    (effects : List (String × FunctionEffect)) (s : Stmt) : Bool :=
  s.anyDeep (stmtReadsStateOrEnvWithFunctionEffectsNode effects)

def stmtListReadsStateOrEnvWithFunctionEffects
    (effects : List (String × FunctionEffect)) (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList (stmtReadsStateOrEnvWithFunctionEffectsNode effects) stmts

def matchBranchesReadStateOrEnvWithFunctionEffects
    (effects : List (String × FunctionEffect))
    (branches : List (String × List String × List Stmt)) : Bool :=
  branches.any fun (_, _, body) => stmtListReadsStateOrEnvWithFunctionEffects effects body

private def functionEffectWithFunctionEffects
    (effects : List (String × FunctionEffect)) (fn : FunctionSpec) : FunctionEffect :=
  { writesState := stmtListWritesStateWithFunctionEffects effects fn.body
    readsStateOrEnv := stmtListReadsStateOrEnvWithFunctionEffects effects fn.body }

private def inferFunctionEffectsStep
    (functions : List FunctionSpec) (effects : List (String × FunctionEffect)) :
    List (String × FunctionEffect) :=
  functions.map fun fn => (fn.name, functionEffectWithFunctionEffects effects fn)

private def iterateFunctionEffects
    (functions : List FunctionSpec) : Nat → List (String × FunctionEffect) →
    List (String × FunctionEffect)
  | 0, effects => effects
  | fuel + 1, effects =>
      iterateFunctionEffects functions fuel (inferFunctionEffectsStep functions effects)

def inferFunctionEffects (functions : List FunctionSpec) : List (String × FunctionEffect) :=
  -- Start optimistic and iterate once per function edge so internal-call read/write
  -- effects propagate through helper chains and cycles before mutability validation.
  let initial := functions.map fun fn => (fn.name, { writesState := false, readsStateOrEnv := false })
  iterateFunctionEffects functions (functions.length + 1) initial

def validateFunctionSpecMutability
    (effects : List (String × FunctionEffect)) (spec : FunctionSpec) : Except String Unit := do
  let effect := functionEffectWithFunctionEffects effects spec
  if spec.isView && effect.writesState then
    throw s!"Compilation error: function '{spec.name}' is marked view but writes state ({issue734Ref})"
  if spec.isPure && effect.writesState then
    throw s!"Compilation error: function '{spec.name}' is marked pure but writes state ({issue734Ref})"
  if spec.isPure && effect.readsStateOrEnv then
    throw s!"Compilation error: function '{spec.name}' is marked pure but reads state/environment ({issue734Ref})"

/-- Node-local classifier: is this statement itself a persistent-storage
    write? Covers all `setStorage*`, `setMapping*`, `storageArray*`,
    `setStructMember*`, and `tstore` constructors plus storage-writing raw
    Yul fragments. Events, local variables, and memory writes are NOT
    considered persistent state writes for CEI purposes.
    (#1728, Axis 2 Step 2a) -/
def stmtIsPersistentWriteNode : Stmt → Bool
  | Stmt.setStorage _ _ | Stmt.setStorageAddr _ _ | Stmt.setStorageWord _ _ _
  | Stmt.storageArrayPush _ _ | Stmt.storageArrayPop _ | Stmt.setStorageArrayElement _ _ _
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMappingChain _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _
  | Stmt.tstore _ _  -- transient storage persists across calls within a transaction
  => true
  | Stmt.unsafeYul fragment =>
      !fragment.scopeEffects.storageWrites.isEmpty || fragment.mechanics.contains .tstore
  | _ => false

/-- Check whether a statement contains a persistent-storage write, recursing
    into `ite`/`forEach`/`unsafeBlock`/`matchAdt` bodies via the canonical
    `Stmt.anyDeep`. -/
def stmtIsPersistentWrite (s : Stmt) : Bool :=
  s.anyDeep stmtIsPersistentWriteNode

def stmtListContainsPersistentWrite (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList stmtIsPersistentWriteNode stmts

def matchBranchesPersistentWrite (branches : List (String × List String × List Stmt)) : Bool :=
  branches.any fun (_, _, body) => stmtListContainsPersistentWrite body

/-- Conservative node-local variant of `stmtIsPersistentWriteNode` for CEI
    validation. Returns `true` for internal calls and internal call
    assignments because their callee bodies may write to storage but we
    cannot inspect them at single-function validation scope. -/
def stmtMayPersistentlyWriteNode : Stmt → Bool
  | Stmt.internalCall _ _ | Stmt.internalCallAssign _ _ _ => true
  | Stmt.ecm mod _ => mod.writesState
  | s => stmtIsPersistentWriteNode s

def stmtMayPersistentlyWrite (s : Stmt) : Bool :=
  s.anyDeep stmtMayPersistentlyWriteNode

def stmtListMayPersistentlyWrite (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList stmtMayPersistentlyWriteNode stmts

def matchBranchesMayPersistentlyWrite (branches : List (String × List String × List Stmt)) : Bool :=
  branches.any fun (_, _, body) => stmtListMayPersistentlyWrite body

mutual
/-- CEI analysis: walk a statement list sequentially and return a descriptive
    violation string if a persistent-storage write occurs after any statement
    that is or contains an external call.  Returns `none` if compliant.
    For `ite`, each branch is checked independently AND if either branch contains
    an external call, subsequent statements must not write state.
    For `forEach`, the body is checked and if it contains an external call the
    loop is treated as an interaction for subsequent statements.
    (#1728, Axis 2 Step 2a) -/
def stmtListCEIViolation : List Stmt → Bool → Option String
  | [], _ => none
  | s :: rest, seenCall =>
      -- First, check for CEI violation within this statement itself (propagating seenCall)
      match stmtInternalCEIViolation s seenCall with
      | some msg => some msg
      | none =>
          -- For compound statements (ite, forEach, unsafeBlock, matchAdt), the internal
          -- CEI check above already verified ordering within the statement's branches.
          let isCompound := match s with
            | Stmt.ite _ _ _ | Stmt.forEach _ _ _ | Stmt.forEachSetBit _ _ _ | Stmt.unsafeBlock _ _
            | Stmt.matchAdt _ _ _ => true
            | _ => false
          -- Update seenCall conservatively: statement-form internal calls may
          -- perform interactions inside the callee, so callers must treat them
          -- as interaction barriers before any later persistent write.
          let newSeenCall := seenCall || stmtMayContainExternalCall s
          -- Write check: use `stmtMayPersistentlyWrite` which conservatively treats
          -- internal calls as potential writes (since callee bodies may write storage
          -- but are not visible at this scope).  This catches the pattern:
          --   externalCallBind(...)        -- seenCall becomes true
          --   internalCall(helper, [...])  -- may write storage → flagged
          if !isCompound && seenCall && stmtMayPersistentlyWrite s then
            some "state write after external call"
          else if !isCompound && stmtContainsExternalCall s && stmtIsPersistentWrite s then
            some "state write in same statement as external call"
          else
            stmtListCEIViolation rest newSeenCall
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

/-- Check for CEI violations within a single compound statement (ite, forEach).
    Accepts `seenCall` from the enclosing context so that an external call before
    an `ite` correctly flags writes inside either branch.
    Returns a descriptive string if a violation is found within the statement's
    own nested structure. -/
def stmtInternalCEIViolation : Stmt → Bool → Option String
  | Stmt.ite cond thenBranch elseBranch, seenCall =>
      -- Include external calls from the condition expression itself, so
      -- `if externalCall(...) then setStorage ...` is correctly flagged
      let condSeenCall := seenCall || exprMayContainExternalCall cond
      match stmtListCEIViolation thenBranch condSeenCall with
      | some msg => some s!"in if-then branch: {msg}"
      | none =>
          match stmtListCEIViolation elseBranch condSeenCall with
          | some msg => some s!"in if-else branch: {msg}"
          | none => none
  | Stmt.forEach _ count body, seenCall | Stmt.forEachSetBit _ count body, seenCall =>
      -- In a loop, if the body has both an external call and a state write,
      -- a second iteration would violate CEI even if the first doesn't
      let bodyHasCall := body.any stmtMayContainExternalCall
      let bodyHasWrite := body.any stmtMayPersistentlyWrite
      if bodyHasCall && bodyHasWrite then
        some "loop body contains both external call and state write (subsequent iterations would violate CEI)"
      else
        -- Include external calls from the loop count expression, so
        -- `forEach i (externalCall ...) do setStorage ...` is correctly flagged
        let countSeenCall := seenCall || exprMayContainExternalCall count
        match stmtListCEIViolation body countSeenCall with
        | some msg => some s!"in loop body: {msg}"
        | none => none
  | Stmt.unsafeBlock _ body, seenCall =>
      match stmtListCEIViolation body seenCall with
      | some msg => some s!"in unsafe block: {msg}"
      | none => none
  | Stmt.matchAdt _ scrutinee branches, seenCall =>
      -- Include external calls from the scrutinee expression, so
      -- `match adtTag (externalCall ...) { ... setStorage ... }` is correctly flagged
      let scrutineeSeenCall := seenCall || exprMayContainExternalCall scrutinee
      matchBranchesCEIViolation branches scrutineeSeenCall
  | Stmt.unsafeYul fragment, seenCall =>
      -- A raw Yul fragment whose mechanics include an external interaction must be
      -- treated like a call for CEI purposes. Flag a violation when a storage write
      -- happens after a prior external call, or within a fragment that both calls
      -- out and writes storage.
      let fragmentCalls :=
        fragment.mechanics.contains .call ||
          fragment.mechanics.contains .staticcall ||
          fragment.mechanics.contains .delegatecall ||
          yulStmtListContainsExternalCall fragment.stmts
      let fragmentWrites :=
        !fragment.scopeEffects.storageWrites.isEmpty ||
          fragment.mechanics.contains .storageWrite ||
          fragment.mechanics.contains .tstore
      if (seenCall || fragmentCalls) && fragmentWrites then
        some "raw Yul fragment writes state after an external call"
      else
        none
  | _, _ => none
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def matchBranchesCEIViolation : List (String × List String × List Stmt) → Bool → Option String
  | [], _ => none
  | (variantName, _, body) :: rest, seenCall =>
      match stmtListCEIViolation body seenCall with
      | some msg => some s!"in match branch '{variantName}': {msg}"
      | none => matchBranchesCEIViolation rest seenCall
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

/-- Node-local classifier lifted with the canonical `Expr.anyDeep`. -/
def exprContainsAdtConstructNode : Expr → Bool
  | Expr.adtConstruct _ _ _ => true
  | _ => false

def exprContainsAdtConstruct (e : Expr) : Bool :=
  e.foldBool exprContainsAdtConstructNode

def exprContainsAdtConstruct_viaFold (e : Expr) : Bool :=
  Expr.foldBool exprContainsAdtConstructNode e

theorem exprContainsAdtConstruct_eq_viaFold (e : Expr) :
    exprContainsAdtConstruct e = exprContainsAdtConstruct_viaFold e := by
  rfl

def exprListContainsAdtConstruct (es : List Expr) : Bool :=
  es.any exprContainsAdtConstruct

/-- Node-local ADT-construction placement check; nested statement bodies are
    reached via the canonical `Stmt.forDeepM`. -/
def validateNoUnsupportedAdtConstructNode : Stmt → Except String Unit
  | Stmt.setStorage _ (Expr.adtConstruct _ _ args) =>
      if exprListContainsAdtConstruct args then
        throw "Compilation error: ADT construction arguments cannot themselves contain ADT construction; construct nested ADTs in storage explicitly."
      else
        pure ()
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value
  | Stmt.setStorageAddr _ value | Stmt.setImmutable _ value | Stmt.setStorageWord _ _ value | Stmt.storageArrayPush _ value
  | Stmt.setStorageArrayElement _ _ value | Stmt.setMapping _ _ value
  | Stmt.setMappingUint _ _ value | Stmt.setMappingWord _ _ _ value
  | Stmt.setMapping2 _ _ _ value | Stmt.setMapping2Word _ _ _ _ value
  | Stmt.setMappingPackedWord _ _ _ _ value
  | Stmt.setMappingChain _ _ value | Stmt.setStructMember _ _ _ value
  | Stmt.setStructMember2 _ _ _ _ value | Stmt.require value _
  | Stmt.return value =>
      if exprContainsAdtConstruct value then
        throw "Compilation error: ADT construction is only supported as the direct value of setStorage for ADT storage fields; expression-position ADT values are not scalar Yul expressions."
      else
        pure ()
  | Stmt.requireError cond _ args =>
      if exprContainsAdtConstruct cond || exprListContainsAdtConstruct args then
        throw "Compilation error: ADT construction is only supported as the direct value of setStorage for ADT storage fields; expression-position ADT values are not scalar Yul expressions."
      else
        pure ()
  | Stmt.revertError _ args | Stmt.returnValues args | Stmt.emit _ args =>
      if exprListContainsAdtConstruct args then
        throw "Compilation error: ADT construction is only supported as the direct value of setStorage for ADT storage fields; expression-position ADT values are not scalar Yul expressions."
      else
        pure ()
  | Stmt.rawLog topics dataOffset dataSize =>
      if exprListContainsAdtConstruct topics || exprContainsAdtConstruct dataOffset ||
          exprContainsAdtConstruct dataSize then
        throw "Compilation error: ADT construction is only supported as the direct value of setStorage for ADT storage fields; expression-position ADT values are not scalar Yul expressions."
      else
        pure ()
  | Stmt.ite cond _ _ => do
      if exprContainsAdtConstruct cond then
        throw "Compilation error: ADT construction cannot be used as an if condition."
  | Stmt.forEach _ count _ | Stmt.forEachSetBit _ count _ => do
      if exprContainsAdtConstruct count then
        throw "Compilation error: ADT construction cannot be used as a loop bound."
  | Stmt.unsafeBlock _ _ =>
      pure ()
  | Stmt.matchAdt _ scrutinee _ => do
      if exprContainsAdtConstruct scrutinee then
        throw "Compilation error: ADT construction cannot be used as a match scrutinee; match storage-backed ADT tags instead."
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args
  | Stmt.externalCallBind _ _ args | Stmt.tryExternalCallBind _ _ _ args
  | Stmt.ecm _ args =>
      if exprListContainsAdtConstruct args then
        throw "Compilation error: ADT construction cannot be passed as a call argument; ABI/function boundary ADT lowering is not implemented."
      else
        pure ()
  | Stmt.mstore offset value | Stmt.tstore offset value => do
      if exprContainsAdtConstruct offset || exprContainsAdtConstruct value then
        throw "Compilation error: ADT construction cannot be used in raw memory/transient-storage operations."
  | Stmt.calldatacopy destOffset sourceOffset size
  | Stmt.returndataCopy destOffset sourceOffset size => do
      if exprContainsAdtConstruct destOffset || exprContainsAdtConstruct sourceOffset ||
          exprContainsAdtConstruct size then
        throw "Compilation error: ADT construction cannot be used in copy offsets or sizes."
  | Stmt.storageArrayPop _ | Stmt.returnArray _ | Stmt.returnBytes _
  | Stmt.returnStorageWords _ | Stmt.returnCodeData _ | Stmt.revertReturndata | Stmt.stop =>
      pure ()
  | Stmt.unsafeYul fragment =>
      if fragment.obligations.isEmpty then
        throw s!"Compilation error: unsafe Yul fragment '{fragment.label}' must declare at least one local proof obligation."
      else
        validateUnsafeYulDeclaredScopeEffects fragment

def validateNoUnsupportedAdtConstructInStmt (stmt : Stmt) : Except String Unit :=
  stmt.checkRec validateNoUnsupportedAdtConstructNode

def validateNoUnsupportedAdtConstructInStmtList (stmts : List Stmt) : Except String Unit :=
  Stmt.checkRecList validateNoUnsupportedAdtConstructNode stmts

def validateNoUnsupportedAdtConstructInBranches
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  Stmt.checkRecBranches validateNoUnsupportedAdtConstructNode branches

def validateNoUnsupportedAdtConstructInStmt_viaFold
    (stmt : Stmt) : Except String Unit :=
  Stmt.checkRec validateNoUnsupportedAdtConstructNode stmt

def validateNoUnsupportedAdtConstructInStmtList_viaFold
    (stmts : List Stmt) : Except String Unit :=
  Stmt.checkRecList validateNoUnsupportedAdtConstructNode stmts

def validateNoUnsupportedAdtConstructInBranches_viaFold
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  Stmt.checkRecBranches validateNoUnsupportedAdtConstructNode branches

theorem validateNoUnsupportedAdtConstructInStmt_eq_viaFold (stmt : Stmt) :
    validateNoUnsupportedAdtConstructInStmt stmt =
      validateNoUnsupportedAdtConstructInStmt_viaFold stmt := by
  rfl

theorem validateNoUnsupportedAdtConstructInStmtList_eq_viaFold (stmts : List Stmt) :
    validateNoUnsupportedAdtConstructInStmtList stmts =
      validateNoUnsupportedAdtConstructInStmtList_viaFold stmts := by
  rfl

theorem validateNoUnsupportedAdtConstructInBranches_eq_viaFold
    (branches : List (String × List String × List Stmt)) :
    validateNoUnsupportedAdtConstructInBranches branches =
      validateNoUnsupportedAdtConstructInBranches_viaFold branches := by
  rfl

def validateFunctionSpec (spec : FunctionSpec) : Except String Unit := do
  let rawYulObligations :=
    Stmt.foldList
      (fun acc _ md => acc ++ md.localObligations)
      []
      spec.body
  if spec.body.any (fun stmt =>
      stmt.fold (fun acc s _ =>
        match s with
        | Stmt.unsafeYul fragment => acc || fragment.obligations.isEmpty
        | _ => acc) false) then
    throw s!"Compilation error: function '{spec.name}' contains an unsafe Yul fragment without explicit local proof obligations."
  -- Check for unsafe boundary mechanics outside `unsafe "reason" do` blocks.
  -- Mechanics inside `unsafe` blocks are documented by the reason string and
  -- do not independently require `local_obligations` (#1728, Phase 6 Step 6b).
  let unguardedMechanics := collectUnguardedUnsafeBoundaryMechanicsFromStmts spec.body
  if !unguardedMechanics.isEmpty && spec.localObligations.isEmpty && rawYulObligations.isEmpty then
    throw s!"Compilation error: function '{spec.name}' uses low-level/assembly mechanic(s) {String.intercalate ", " unguardedMechanics} outside an unsafe block without any local_obligations entry ({issue1424Ref}). Wrap the low-level code in `unsafe \"reason\" do` or add local_obligations [...] to make the trust boundary explicit."
  if spec.isPayable && (spec.isView || spec.isPure) then
    throw s!"Compilation error: function '{spec.name}' cannot be both payable and view/pure ({issue586Ref})"
  if spec.isView && spec.isPure then
    throw s!"Compilation error: function '{spec.name}' cannot be both view and pure; use exactly one mutability marker ({issue586Ref})"
  if spec.body.any stmtContainsUnsafeLogicalCallLike then
    throw s!"Compilation error: function '{spec.name}' uses Expr.logicalAnd/Expr.logicalOr/Expr.ite or arithmetic helpers (mulDivUp/wDivUp/min/max) with call-like operand(s) that would be duplicated in Yul output ({issue748Ref}). Move call-like expressions into Stmt.letVar before combining."
  validateAdtPayloadParamNameCollisions s!"function '{spec.name}'" spec.params spec.body
  validateNoUnsupportedAdtConstructInStmtList spec.body
  let returns ← functionReturns spec
  spec.body.forM (validateReturnShapesInStmt spec.name spec.params returns spec.isInternal)
  if !returns.isEmpty && !stmtListAlwaysReturnsOrReverts spec.body then
    throw s!"Compilation error: function '{spec.name}' declares return values but not all control-flow paths end in return/revert ({issue738Ref})"
  spec.body.forM (validateStmtParamReferences spec.name spec.params)
  -- Validate modifies annotation: if declared, every written field must be in the set
  if !spec.modifies.isEmpty then
    -- Reject modifies() when the body contains calls whose write sets cannot be
    -- statically tracked (internal calls, external calls, ECM invocations).
    if stmtListHasUntrackableWrites spec.body then
      throw s!"Compilation error: function '{spec.name}' is annotated modifies({String.intercalate ", " spec.modifies}) but contains internal call statements whose write sets cannot be verified statically. Remove the modifies annotation or inline the called logic."
    let writtenFields := (stmtListWrittenFields spec.body).eraseDups
    for field in writtenFields do
      if !spec.modifies.contains field then
        throw s!"Compilation error: function '{spec.name}' is annotated modifies({String.intercalate ", " spec.modifies}) but writes to undeclared field '{field}'"
  -- Validate no_external_calls annotation: reject external call statements.
  -- Uses the conservative `stmtMayContainExternalCall` which also flags internal calls
  -- (since callee bodies may contain external calls not visible at this scope).
  if spec.noExternalCalls && spec.body.any stmtMayContainExternalCall then
    throw s!"Compilation error: function '{spec.name}' is annotated no_external_calls but contains statements that may perform external calls (including internal function calls whose bodies cannot be verified here)"
  -- An internal function annotated `nonreentrant(<lock>)` would receive
  -- the CEI exemption below without ever materialising a runtime guard
  -- — `attachNonReentrantGuard` (#1893) only injects the transient-storage
  -- prologue for external dispatch entries. Reject that combination at
  -- the compilation-model boundary too, so callers that build specs
  -- without going through the macro pipeline can't silently get an
  -- unguarded post-interaction-write window.
  if spec.isInternal && spec.nonReentrantLock.isSome then
    throw s!"Compilation error: internal function '{spec.name}' carries a nonreentrant(<lock>) annotation, but the synthesised reentrancy guard only runs on external entrypoints. Move the annotation to the public caller or drop it ({issue1728Ref})."
  -- CEI enforcement: reject state writes after external calls unless the
  -- function explicitly records a trust-surface opt-out. `cei_safe`
  -- remains a proof-only hook (a discharge obligation rather than a
  -- runtime guard), so it does NOT exempt CEI here. `nonreentrant(field)`
  -- on an external entrypoint synthesises a real transient-storage
  -- reentrancy guard during contract assembly (#1893), so the
  -- post-interaction-write window is closed at runtime — that justifies
  -- exempting CEI for the annotation, but only for externals (internals
  -- are already rejected above). `allow_post_interaction_writes` is the
  -- legacy untyped opt-out for callers that audit CEI manually.
  let ceiExempt :=
    spec.allowPostInteractionWrites ||
      (spec.nonReentrantLock.isSome && !spec.isInternal)
  if !ceiExempt then
    match stmtListCEIViolation spec.body false with
    | some violation =>
        throw s!"Compilation error: function '{spec.name}' violates CEI (Checks-Effects-Interactions) ordering: {violation}. Reorder state writes before external calls, or annotate with allow_post_interaction_writes / nonreentrant(<lock>) to opt out ({issue1728Ref})"
    | none => pure ()
  validateFunctionIdentifierReferences spec

/-- Cross-function reentrancy gate (fail-closed). A function that makes a direct
    external call opens a reentrancy window: while control is handed to an
    external callee, another entrypoint can re-enter and observe or exploit this
    contract's mid-update state (the Midnight `take`/`liquidate` class of bug,
    which single-function CEI does NOT prevent — even a CEI-clean function leaves
    a transiently-exploitable state live during its callback). Such a function
    must therefore carry a *sound* reentrancy disposition: either a runtime
    `nonreentrant(<lock>)` guard (closes the window at the external dispatch
    boundary, #1893) or an explicit audited `reentrancy_trusted` assertion.
    `cei_safe` / `allow_post_interaction_writes` only concern single-function CEI
    and are intentionally NOT accepted here. `view`/`pure` functions are exempt:
    a read-only (staticcall) context cannot mutate state and so cannot open a
    state-corrupting reentrancy window. For the same reason `stmtOpensReentrancyWindow`
    (unlike `stmtContainsExternalCall`) does not count a `staticcall`-summarised
    ECM — precompiles, `keccak`/`sha256`, ABI encoding, view-only reads — which
    the EVM runs in a static context where any state mutation reverts.

    This runs as a dedicated pass *after* call well-formedness validation
    (`validateExternalCallTargetsInFunction`), so a malformed external call
    surfaces its structural error first; the reentrancy policy only judges
    otherwise well-formed external calls. -/
def validateReentrancyDisposition (spec : FunctionSpec) : Except String Unit := do
  if spec.body.any stmtOpensReentrancyWindow
      && !spec.isView && !spec.isPure
      && !(spec.nonReentrantLock.isSome || spec.reentrancyTrusted) then
    throw s!"Compilation error: function '{spec.name}' makes an external call but declares no reentrancy disposition. An external call hands control to an untrusted callee that may re-enter another entrypoint while this contract's state is mid-update (cross-function reentrancy). Add `nonreentrant(<lock>)` to synthesise a runtime guard, or `reentrancy_trusted` to assert — and own — that every external callee is trusted not to re-enter ({issue1728Ref}). cei_safe / allow_post_interaction_writes cover only single-function CEI and do not satisfy this gate."

/-- Node-local constructor return check; nested statement bodies are reached
    via the canonical `Stmt.forDeepM`. -/
def validateNoRuntimeReturnsInConstructorNode : Stmt → Except String Unit
  | Stmt.return _ | Stmt.returnValues _ | Stmt.returnArray _
  | Stmt.returnBytes _ | Stmt.returnStorageWords _ | Stmt.returnCodeData _ =>
      throw "Compilation error: constructor must not return runtime data directly"
  | _ => pure ()

def validateNoRuntimeReturnsInConstructorStmt (stmt : Stmt) : Except String Unit :=
  stmt.checkRec validateNoRuntimeReturnsInConstructorNode

def validateNoRuntimeReturnsInConstructorStmtList (stmts : List Stmt) : Except String Unit :=
  Stmt.checkRecList validateNoRuntimeReturnsInConstructorNode stmts

def validateNoRuntimeReturnsInConstructorBranches
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  Stmt.checkRecBranches validateNoRuntimeReturnsInConstructorNode branches

def validateNoRuntimeReturnsInConstructorStmt_viaFold
    (stmt : Stmt) : Except String Unit :=
  Stmt.checkRec validateNoRuntimeReturnsInConstructorNode stmt

def validateNoRuntimeReturnsInConstructorStmtList_viaFold
    (stmts : List Stmt) : Except String Unit :=
  Stmt.checkRecList validateNoRuntimeReturnsInConstructorNode stmts

def validateNoRuntimeReturnsInConstructorBranches_viaFold
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  Stmt.checkRecBranches validateNoRuntimeReturnsInConstructorNode branches

theorem validateNoRuntimeReturnsInConstructorStmt_eq_viaFold (stmt : Stmt) :
    validateNoRuntimeReturnsInConstructorStmt stmt =
      validateNoRuntimeReturnsInConstructorStmt_viaFold stmt := by
  rfl

theorem validateNoRuntimeReturnsInConstructorStmtList_eq_viaFold
    (stmts : List Stmt) :
    validateNoRuntimeReturnsInConstructorStmtList stmts =
      validateNoRuntimeReturnsInConstructorStmtList_viaFold stmts := by
  rfl

theorem validateNoRuntimeReturnsInConstructorBranches_eq_viaFold
    (branches : List (String × List String × List Stmt)) :
    validateNoRuntimeReturnsInConstructorBranches branches =
      validateNoRuntimeReturnsInConstructorBranches_viaFold branches := by
  rfl

def validateConstructorSpec (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      let rawYulObligations :=
        Stmt.foldList
          (fun acc _ md => acc ++ md.localObligations)
          []
          spec.body
      if spec.body.any (fun stmt =>
          stmt.fold (fun acc s _ =>
            match s with
            | Stmt.unsafeYul fragment => acc || fragment.obligations.isEmpty
            | _ => acc) false) then
        throw "Compilation error: constructor contains an unsafe Yul fragment without explicit local proof obligations."
      let unguardedMechanics := collectUnguardedUnsafeBoundaryMechanicsFromStmts spec.body
      if !unguardedMechanics.isEmpty && spec.localObligations.isEmpty && rawYulObligations.isEmpty then
        throw s!"Compilation error: constructor uses low-level/assembly mechanic(s) {String.intercalate ", " unguardedMechanics} outside an unsafe block without any local_obligations entry ({issue1424Ref}). Wrap the low-level code in `unsafe \"reason\" do` or add local_obligations [...] to make the trust boundary explicit."
      if spec.body.any stmtContainsUnsafeLogicalCallLike then
        throw s!"Compilation error: constructor uses Expr.logicalAnd/Expr.logicalOr/Expr.ite or arithmetic helpers (mulDivUp/wDivUp/min/max) with call-like operand(s) that would be duplicated in Yul output ({issue748Ref}). Move call-like expressions into Stmt.letVar before combining."
      validateAdtPayloadParamNameCollisions "constructor" spec.params spec.body
      validateNoUnsupportedAdtConstructInStmtList spec.body
      spec.body.forM validateNoRuntimeReturnsInConstructorStmt
      spec.body.forM (validateStmtParamReferences "constructor" spec.params)
      validateConstructorIdentifierReferences ctor

end Compiler.CompilationModel
