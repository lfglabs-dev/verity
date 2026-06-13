/-
  Compiler.CompilationModel.Compile: Compilation pipeline implementation

  This module defines a declarative way to model contracts for compilation,
  eliminating manual IR writing while keeping the system simple and maintainable.

  Philosophy:
  - Contracts specify their structure declaratively
  - Compiler generates IR automatically from the spec
  - Reduces boilerplate and eliminates manual slot/selector management

  Features:
  - Storage fields with automatic slot assignment (uint256, address, mapping)
  - Flexible mapping types: Address→Uint256, Uint256→Uint256, nested mappings (#154)
  - Functions with automatic selector computation
  - Guards and access control patterns
  - If/else branching and bounded loops (#179)
  - Array/bytes parameter types and dynamic calldata (#180)
  - Internal function composition (#181)
  - Event emission (#153)
  - Verified external library integration (#184)
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.AbiEncoding
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.EcmAxiomCollection
import Compiler.CompilationModel.EventEmission
import Compiler.CompilationModel.InternalArgs
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.LayoutValidation
import Compiler.CompilationModel.MappingWrites
import Compiler.CompilationModel.UsageAnalysis
import Compiler.CompilationModel.ValidationHelpers
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.CompilationModel.ExpressionCompile
import Compiler.CompilationModel.StorageWrites
import Compiler.CompilationModel.Validation
import Compiler.CompilationModel.AdtStorageLayout

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

/-- Single bridge from typed unsafe/raw Yul fragments into the EVMYul AST.
    Proof obligations and trust metadata live on `UnsafeYulFragment`; this
    function is intentionally the only compiler lowering point for that escape
    hatch. -/
def unsafeYulToEVMYul (fragment : UnsafeYulFragment) : List YulStmt :=
  fragment.stmts

theorem unsafeYulToEVMYul_eq (fragment : UnsafeYulFragment) :
    unsafeYulToEVMYul fragment = fragment.stmts := rfl

private def compileAdtStorageWrite (fields : List Field)
    (dynamicSource : DynamicDataSource) (adtTypes : List AdtTypeDef)
    (storageField adtName variantName : String) (args : List Expr) :
    Except String (List YulStmt) := do
  let adt ← lookupAdtTypeDef adtTypes adtName
  let variant ← lookupAdtVariant adt variantName
  if args.length != variant.fields.length then
    throw s!"Compilation error: ADT construct '{adtName}.{variantName}' expects {variant.fields.length} payload value(s), got {args.length}"
  let (baseSlot, aliasSlots) ←
    match findFieldWithResolvedSlot fields storageField with
    | some (field, slot) =>
        match field.ty with
        | .adt fieldAdtName fieldMaxFields =>
          if fieldAdtName != adtName then
            throw s!"Compilation error: storage field '{storageField}' stores ADT '{fieldAdtName}', not '{adtName}'"
          else if fieldMaxFields < adtMaxFieldSlots adt then
            throw s!"Compilation error: storage field '{storageField}' reserves {fieldMaxFields} ADT payload slot(s), but ADT '{adtName}' needs {adtMaxFieldSlots adt}"
          else
            pure (slot, field.aliasSlots)
        | _ =>
            throw s!"Compilation error: storage field '{storageField}' is not ADT-typed"
    | none => throw s!"Compilation error: unknown storage field '{storageField}' for ADT construct '{adtName}.{variantName}'"
  let baseSlots := baseSlot :: aliasSlots
  let argExprs ← compileExprList fields dynamicSource args
  let payloadBindings :=
    argExprs.zipIdx.map fun (argExpr, idx) =>
      YulStmt.let_ s!"__adt_payload_{idx}" argExpr
  let payloadExprs :=
    argExprs.zipIdx.map fun (_, idx) =>
      YulExpr.ident s!"__adt_payload_{idx}"
  let tagStores := baseSlots.map fun slot =>
    compileAdtTagWrite (YulExpr.lit slot) variant.tag
  let payloadStores :=
    baseSlots.flatMap fun slot =>
      payloadExprs.zipIdx.map fun (argExpr, idx) =>
        compileAdtFieldWrite (YulExpr.lit slot) idx argExpr
  let clearStores :=
    baseSlots.flatMap fun slot =>
      (List.range (adtMaxFieldSlots adt)).drop args.length |>.map fun idx =>
        compileAdtFieldWrite (YulExpr.lit slot) idx (YulExpr.lit 0)
  pure (payloadBindings ++ tagStores ++ payloadStores ++ clearStores)

/-- Scope visible while compiling a `Stmt.forEach` body. The loop's synthetic
counters `__forEach_idx`/`__forEach_count` are live across the whole body (Yul
for-loop init variables are in scope in the body), so they must be tracked while
compiling it. Otherwise a nested `forEach` re-derives the same names and the inner
`let` collides with the outer one ("Variable name already taken in this scope").
This is defeq to the codegen's inline `idxName :: countName :: varName :: inScopeNames`,
so the generated Yul is unchanged; it exists as a named handle for the proofs. -/
def forEachBodyScope (inScopeNames : List String) (varName : String)
    (count : Expr) (body : List Stmt) : List String :=
  let forUsedNames := varName :: (inScopeNames ++ collectExprNames count ++ collectStmtListNames body)
  let idxName := pickFreshName "__forEach_idx" forUsedNames
  let countName := pickFreshName "__forEach_count" (idxName :: forUsedNames)
  idxName :: countName :: varName :: inScopeNames

-- Compile statement to Yul (using mutual recursion for lists).
-- When isInternal=true, Stmt.return compiles to `__ret := value; leave` so internal
-- function execution terminates immediately without exiting the outer EVM call.
mutual
def compileStmtList (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := [])
    (adtTypes : List AdtTypeDef := [])
    (stmts : List Stmt) (internalFunctions : List FunctionSpec := []) :
    Except String (List YulStmt) :=
  match stmts with
  | [] => pure []
  | s :: ss => do
      let head ← compileStmt fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes s internalFunctions
      let nextScopeNames := collectStmtNames s ++ inScopeNames
      let tail ← compileStmtList fields events errors dynamicSource internalRetNames isInternal nextScopeNames adtTypes ss internalFunctions
      pure (head ++ tail)

def compileStmt (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := [])
    (adtTypes : List AdtTypeDef := [])
    (stmt : Stmt) (internalFunctions : List FunctionSpec := []) :
    Except String (List YulStmt)
  := match stmt with
  | Stmt.letVar name value => do
      pure [YulStmt.let_ name (← compileExprWithInternals fields dynamicSource internalFunctions value)]
  | Stmt.assignVar name value => do
      pure [YulStmt.assign name (← compileExprWithInternals fields dynamicSource internalFunctions value)]
  | Stmt.setStorage field value =>
      match adtTypes with
      | [] => compileSetStorage fields dynamicSource field value false internalFunctions
      | _ =>
          match value with
          | Expr.adtConstruct adtName variantName args =>
              compileAdtStorageWrite fields dynamicSource adtTypes field adtName variantName args
          | _ =>
              compileSetStorage fields dynamicSource field value false internalFunctions
  | Stmt.setStorageAddr field value =>
      compileSetStorage fields dynamicSource field value true internalFunctions
  | Stmt.setStorageWord field wordOffset value =>
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) => do
          let valueExpr ← compileExprWithInternals fields dynamicSource internalFunctions value
          let slotExpr (baseSlot : Nat) :=
            if wordOffset == 0 then YulExpr.lit baseSlot
            else YulExpr.call "add" [YulExpr.lit baseSlot, YulExpr.lit wordOffset]
          match f.aliasSlots with
          | [] =>
              pure [YulStmt.expr (YulExpr.call "sstore" [slotExpr slot, valueExpr])]
          | _ =>
              pure [
                YulStmt.block (
                  [YulStmt.let_ "__compat_value" valueExpr] ++
                  (slot :: f.aliasSlots).map (fun writeSlot =>
                    YulStmt.expr (YulExpr.call "sstore" [
                      slotExpr writeSlot,
                      YulExpr.ident "__compat_value"
                    ]))
                )
              ]
      | none =>
          throw s!"Compilation error: unknown storage field '{field}' in setStorageWord"
  | Stmt.storageArrayPush field value =>
      compileStorageArrayPush fields dynamicSource field value internalFunctions
  | Stmt.storageArrayPop field =>
      compileStorageArrayPop fields field
  | Stmt.setStorageArrayElement field index value =>
      compileSetStorageArrayElement fields dynamicSource field index value internalFunctions
  | Stmt.setMapping field key value => do
      compileMappingSlotWrite fields field
        (← compileExprWithInternals fields dynamicSource internalFunctions key)
        (← compileExprWithInternals fields dynamicSource internalFunctions value)
        "setMapping"
  | Stmt.setMappingWord field key wordOffset value => do
      compileMappingSlotWrite fields field
        (← compileExprWithInternals fields dynamicSource internalFunctions key)
        (← compileExprWithInternals fields dynamicSource internalFunctions value)
        "setMappingWord"
        wordOffset
  | Stmt.setMappingPackedWord field key wordOffset packed value => do
      compileMappingPackedSlotWrite fields field
        (← compileExprWithInternals fields dynamicSource internalFunctions key)
        (← compileExprWithInternals fields dynamicSource internalFunctions value)
        wordOffset
        packed
        "setMappingPackedWord"
  | Stmt.setMapping2 field key1 key2 value =>
      compileSetMapping2 fields dynamicSource field key1 key2 value internalFunctions
  | Stmt.setMapping2Word field key1 key2 wordOffset value =>
      compileSetMapping2Word fields dynamicSource field key1 key2 wordOffset value internalFunctions
  | Stmt.setMappingUint field key value => do
      compileMappingSlotWrite fields field
        (← compileExprWithInternals fields dynamicSource internalFunctions key)
        (← compileExprWithInternals fields dynamicSource internalFunctions value)
        "setMappingUint"
  | Stmt.setMappingChain field keys value =>
      compileSetMappingChain fields dynamicSource field keys value internalFunctions
  | Stmt.setStructMember field key memberName value =>
      compileSetStructMember fields dynamicSource field key memberName value internalFunctions
  | Stmt.setStructMember2 field key1 key2 memberName value =>
      compileSetStructMember2 fields dynamicSource field key1 key2 memberName value internalFunctions
  | Stmt.require cond message =>
    do
      let failCond ← compileRequireFailCondWithInternals fields dynamicSource internalFunctions cond
      pure [
        YulStmt.if_ failCond (revertWithMessage message)
      ]
  | Stmt.requireError cond errorName args => do
      let failCond ← compileRequireFailCondWithInternals fields dynamicSource internalFunctions cond
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      let argExprs ← compileExprListWithInternals fields dynamicSource internalFunctions args
      let revertStmts ← revertWithCustomError dynamicSource errorDef args argExprs
      pure [YulStmt.if_ failCond revertStmts]
  | Stmt.revertError errorName args => do
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      let argExprs ← compileExprListWithInternals fields dynamicSource internalFunctions args
      revertWithCustomError dynamicSource errorDef args argExprs
  | Stmt.return value =>
    do
      let valueExpr ← compileExprWithInternals fields dynamicSource internalFunctions value
      if isInternal then
        match internalRetNames with
        | retName :: _ => pure [YulStmt.assign retName valueExpr, YulStmt.leave]
        | [] => throw s!"Compilation error: internal return target is missing"
      else
        pure [
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueExpr]),
          YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
  | Stmt.stop => return [YulStmt.expr (YulExpr.call "stop" [])]

  | Stmt.ite cond thenBranch elseBranch => do
      -- If/else: compile to Yul if + negated if (#179)
      let condExpr ← compileExprWithInternals fields dynamicSource internalFunctions cond
      let thenStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes thenBranch internalFunctions
      let elseStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes elseBranch internalFunctions
      if elseBranch.isEmpty then
        -- Simple if (no else)
        pure [YulStmt.if_ condExpr thenStmts]
      else
        -- If/else: cache condition in a block-scoped local to avoid re-evaluation
        -- after then-branch may have mutated state.
        -- Wrapped in block { } and freshened against names seen in this if/else shape
        -- so user locals cannot shadow the compiler-generated temp.
        let iteUsedNames := inScopeNames ++ collectExprNames cond ++ collectStmtListNames thenBranch ++ collectStmtListNames elseBranch
        let iteCondName := pickFreshName "__ite_cond" iteUsedNames
        pure [YulStmt.block [
          YulStmt.let_ iteCondName condExpr,
          YulStmt.if_ (YulExpr.ident iteCondName) thenStmts,
          YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident iteCondName]) elseStmts
        ]]

  | Stmt.forEach varName count body => do
      -- Bounded loop: evaluate `count` once into a cached local, drive iteration
      -- with a fresh internal counter, and assign the user-visible `varName` to
      -- the current counter at the top of each iteration. This matches the source
      -- semantics where `count` is evaluated once and `varName` holds the last
      -- iteration state after the loop rather than the post-incremented counter.
      let countExpr ← compileExprWithInternals fields dynamicSource internalFunctions count
      let forUsedNames := varName :: (inScopeNames ++ collectExprNames count ++ collectStmtListNames body)
      let idxName := pickFreshName "__forEach_idx" forUsedNames
      let countName := pickFreshName "__forEach_count" (idxName :: forUsedNames)
      -- Compile the body with the synthetic counters in scope (see `forEachBodyScope`),
      -- so a nested `forEach` cannot re-derive colliding `__forEach_idx`/`__forEach_count`.
      let bodyStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal (forEachBodyScope inScopeNames varName count body) adtTypes body internalFunctions
      let initStmts := [
        YulStmt.let_ idxName (YulExpr.lit 0),
        YulStmt.let_ countName countExpr,
        YulStmt.let_ varName (YulExpr.lit 0)
      ]
      let condExpr := YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName]
      let postStmts := [YulStmt.assign idxName (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
      let bodyWithBind := YulStmt.assign varName (YulExpr.ident idxName) :: bodyStmts
      pure [YulStmt.for_ initStmts condExpr postStmts bodyWithBind]

  | Stmt.unsafeBlock _ body => do
      -- Unsafe block: transparent wrapper, compile inner body directly (#1728, Axis 6 Step 6a)
      compileStmtList fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes body internalFunctions

  | Stmt.unsafeYul fragment =>
      pure (unsafeYulToEVMYul fragment)

  | Stmt.emit eventName args => do
      compileEmit fields events dynamicSource eventName args internalFunctions

  | Stmt.internalCall functionName args => do
      -- Internal function call as statement (#181)
      let argExprs ← compileInternalCallArgs fields dynamicSource internalFunctions functionName args
      pure [YulStmt.expr (YulExpr.call (internalFunctionYulName functionName) argExprs)]
  | Stmt.internalCallAssign names functionName args => do
      let argExprs ← compileInternalCallArgs fields dynamicSource internalFunctions functionName args
      pure [YulStmt.letMany names (YulExpr.call (internalFunctionYulName functionName) argExprs)]
  | Stmt.externalCallBind resultVars externalName args => do
      let argExprs ← compileExprListWithInternals fields dynamicSource internalFunctions args
      if resultVars.isEmpty then
        pure [YulStmt.expr (YulExpr.call externalName argExprs)]
      else
        pure [YulStmt.letMany resultVars (YulExpr.call externalName argExprs)]
  -- Try-call variant: calls {externalName}_try which returns (success, result...)
  -- instead of reverting on failure. (#1727, Axis 1 Step 5f)
  | Stmt.tryExternalCallBind successVar resultVars externalName args => do
      let argExprs ← compileExprListWithInternals fields dynamicSource internalFunctions args
      let tryFnName := s!"{externalName}_try"
      pure [YulStmt.letMany (successVar :: resultVars) (YulExpr.call tryFnName argExprs)]
  -- NOTE: safeTransfer, safeTransferFrom, externalCallWithReturn, callback, ecrecover
  -- have been removed. Use Stmt.ecm with the appropriate module from Compiler/Modules/.
  | Stmt.ecm mod args => do
      if args.length != mod.numArgs then
        throw s!"ECM '{mod.name}': expected {mod.numArgs} arguments, got {args.length}"
      let compiledArgs ← compileExprListWithInternals fields dynamicSource internalFunctions args
      let ctx : ECM.CompilationContext := {
        isDynamicFromCalldata := dynamicSource == .calldata
      }
      mod.compile ctx compiledArgs
  | Stmt.returnValues values => do
      if isInternal then
        if values.length != internalRetNames.length then
          throw s!"Compilation error: internal return arity mismatch: expected {internalRetNames.length}, got {values.length}"
        else
          let compiled ← compileExprListWithInternals fields dynamicSource internalFunctions values
          let assigns := (internalRetNames.zip compiled).map fun (name, valueExpr) =>
            YulStmt.assign name valueExpr
          pure (assigns ++ [YulStmt.leave])
      else if values.isEmpty then
        pure [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 0])]
      else
        let compiled ← compileExprListWithInternals fields dynamicSource internalFunctions values
        let stores := (compiled.zipIdx.map fun (valueExpr, idx) =>
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (idx * 32), valueExpr]))
        pure (stores ++ [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit (values.length * 32)])])
  | Stmt.returnArray name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      let byteLen := YulExpr.call "mul" [lenIdent, YulExpr.lit 32]
      if isInternal then
        match internalRetNames with
        | offsetRet :: lengthRet :: _ =>
            pure [
              YulStmt.assign offsetRet dataOffset,
              YulStmt.assign lengthRet lenIdent,
              YulStmt.leave
            ]
        | _ =>
            throw s!"Compilation error: internal array return target is missing offset/length registers"
      else
        pure ([
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
        ] ++ dynamicCopyData dynamicSource (YulExpr.lit 64) dataOffset byteLen ++ [
          YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.call "add" [YulExpr.lit 64, byteLen]])
        ])
  | Stmt.returnBytes name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      let tailOffset := YulExpr.call "add" [YulExpr.lit 64, lenIdent]
      let paddedLen :=
        YulExpr.call "and" [
          YulExpr.call "add" [lenIdent, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
      ] ++ dynamicCopyData dynamicSource (YulExpr.lit 64) dataOffset lenIdent ++ [
        YulStmt.expr (YulExpr.call "mstore" [tailOffset, YulExpr.lit 0]),
        YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.call "add" [YulExpr.lit 64, paddedLen]])
      ])
  | Stmt.returnStorageWords name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      pure [
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
        YulStmt.for_
          [YulStmt.let_ "__i" (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident "__i", lenIdent])
          [YulStmt.assign "__i" (YulExpr.call "add" [YulExpr.ident "__i", YulExpr.lit 1])]
          [
            YulStmt.let_ "__slot" (dynamicWordLoad dynamicSource (YulExpr.call "add" [
              dataOffset,
              YulExpr.call "mul" [YulExpr.ident "__i", YulExpr.lit 32]
            ])),
            YulStmt.expr (YulExpr.call "mstore" [
              YulExpr.call "add" [YulExpr.lit 64, YulExpr.call "mul" [YulExpr.ident "__i", YulExpr.lit 32]],
              YulExpr.call "sload" [YulExpr.ident "__slot"]
            ])
          ],
        YulStmt.expr (YulExpr.call "return" [
          YulExpr.lit 0,
          YulExpr.call "add" [YulExpr.lit 64, YulExpr.call "mul" [lenIdent, YulExpr.lit 32]]
        ])
      ]
  | Stmt.returnCodeData pointer => do
      if isInternal then
        throw s!"Compilation error: internal functions cannot use returnCodeData"
      let pointerExpr ← compileExprWithInternals fields dynamicSource internalFunctions pointer
      pure [
        YulStmt.block [
          YulStmt.let_ "__return_code_pointer"
            (YulExpr.call "and" [pointerExpr, YulExpr.hex addressMask]),
          YulStmt.let_ "__return_code_offset" (YulExpr.lit 1),
          YulStmt.let_ "__return_code_extent"
            (YulExpr.call "extcodesize" [YulExpr.ident "__return_code_pointer"]),
          YulStmt.if_
            (YulExpr.call "iszero" [
              YulExpr.call "gt" [
                YulExpr.ident "__return_code_extent",
                YulExpr.ident "__return_code_offset"
              ]
            ])
            [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])],
          YulStmt.let_ "__return_code_size"
            (YulExpr.call "sub" [
              YulExpr.ident "__return_code_extent",
              YulExpr.ident "__return_code_offset"
            ]),
          YulStmt.let_ "__return_code_ptr"
            (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
          YulStmt.expr (YulExpr.call "extcodecopy" [
            YulExpr.ident "__return_code_pointer",
            YulExpr.ident "__return_code_ptr",
            YulExpr.ident "__return_code_offset",
            YulExpr.ident "__return_code_size"
          ]),
          YulStmt.expr (YulExpr.call "return" [
            YulExpr.ident "__return_code_ptr",
            YulExpr.ident "__return_code_size"
          ])
        ]
      ]
  | Stmt.mstore offset value => do
      pure [YulStmt.expr (YulExpr.call "mstore" [
        ← compileExprWithInternals fields dynamicSource internalFunctions offset,
        ← compileExprWithInternals fields dynamicSource internalFunctions value
      ])]
  | Stmt.tstore offset value => do
      pure [YulStmt.expr (YulExpr.call "tstore" [
        ← compileExprWithInternals fields dynamicSource internalFunctions offset,
        ← compileExprWithInternals fields dynamicSource internalFunctions value
      ])]
  | Stmt.calldatacopy destOffset sourceOffset size => do
      pure [YulStmt.expr (YulExpr.call "calldatacopy" [
        ← compileExprWithInternals fields dynamicSource internalFunctions destOffset,
        ← compileExprWithInternals fields dynamicSource internalFunctions sourceOffset,
        ← compileExprWithInternals fields dynamicSource internalFunctions size
      ])]
  | Stmt.returndataCopy destOffset sourceOffset size => do
      pure [YulStmt.expr (YulExpr.call "returndatacopy" [
        ← compileExprWithInternals fields dynamicSource internalFunctions destOffset,
        ← compileExprWithInternals fields dynamicSource internalFunctions sourceOffset,
        ← compileExprWithInternals fields dynamicSource internalFunctions size
      ])]
  | Stmt.revertReturndata =>
      pure [YulStmt.block [
        YulStmt.let_ "__returndata_size" (YulExpr.call "returndatasize" []),
        YulStmt.expr (YulExpr.call "returndatacopy" [
          YulExpr.lit 0,
          YulExpr.lit 0,
          YulExpr.ident "__returndata_size"
        ]),
        YulStmt.expr (YulExpr.call "revert" [
          YulExpr.lit 0,
          YulExpr.ident "__returndata_size"
        ])
      ]]
  | Stmt.rawLog topics dataOffset dataSize => do
      if topics.length > 4 then
        throw s!"Compilation error: rawLog supports at most 4 topics (log0–log4), got {topics.length}"
      let topicExprs ← compileExprListWithInternals fields dynamicSource internalFunctions topics
      let offsetExpr ← compileExprWithInternals fields dynamicSource internalFunctions dataOffset
      let sizeExpr ← compileExprWithInternals fields dynamicSource internalFunctions dataSize
      let logFn := s!"log{topics.length}"
      pure [YulStmt.expr (YulExpr.call logFn ([offsetExpr, sizeExpr] ++ topicExprs))]
  -- ADT pattern match: compile to YulStmt.switch on tag value (#1727 Steps 5c/5d)
  | Stmt.matchAdt adtName scrutinee branches => do
      let def_ ← lookupAdtTypeDef adtTypes adtName
      -- Compile the scrutinee (tag value expression)
      let scrutineeExpr ← compileExprWithInternals fields dynamicSource internalFunctions scrutinee
      -- Extract storage field name from scrutinee for field bindings
      let storageFieldName ← match scrutinee with
        | Expr.adtTag scrutineeAdtName fieldName =>
            if scrutineeAdtName == adtName then
              pure fieldName
            else
              throw s!"Compilation error: matchAdt declared for '{adtName}' but scrutinee reads ADT '{scrutineeAdtName}'"
        | _ => throw s!"Compilation error: matchAdt scrutinee for '{adtName}' must be an adtTag expression"
      let baseSlot ← match findFieldSlot fields storageFieldName with
        | some s => pure s
        | none => throw s!"Compilation error: unknown storage field '{storageFieldName}' for matchAdt on '{adtName}'"
      -- Build switch cases: each branch matches on the variant's tag
      let cases ← compileMatchAdtBranches fields events errors dynamicSource internalRetNames isInternal
        inScopeNames adtTypes internalFunctions def_ baseSlot branches
      -- Default case: revert (should be unreachable for exhaustive matches)
      let defaultCase := [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
      pure [YulStmt.switch scrutineeExpr cases (some defaultCase)]

def compileMatchAdtBranches (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (dynamicSource : DynamicDataSource)
    (internalRetNames : List String) (isInternal : Bool)
    (inScopeNames : List String) (adtTypes : List AdtTypeDef)
    (internalFunctions : List FunctionSpec)
    (def_ : AdtTypeDef) (baseSlot : Nat) :
    List (String × List String × List Stmt) → Except String (List (Nat × List YulStmt))
  | [] => pure []
  | (variantName, boundVarNames, body) :: rest => do
      let variant ← lookupAdtVariant def_ variantName
      if boundVarNames.length != variant.fields.length then
        throw s!"Compilation error: match branch '{variantName}' of ADT '{def_.name}' binds {boundVarNames.length} variables, but the variant has {variant.fields.length} fields"
      -- Bind each variable to sload(baseSlot + 1 + idx)
      let fieldBindings := boundVarNames.zipIdx.map fun (varName, idx) =>
        YulStmt.let_ varName (compileAdtFieldRead (YulExpr.lit baseSlot) idx)
      let bodyStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal
        (boundVarNames.reverse ++ inScopeNames) adtTypes body internalFunctions
      let restCases ← compileMatchAdtBranches fields events errors dynamicSource internalRetNames isInternal
        inScopeNames adtTypes internalFunctions def_ baseSlot rest
      pure ((variant.tag, fieldBindings ++ bodyStmts) :: restCases)
end

theorem compileStmt_unsafeYul
    (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := [])
    (adtTypes : List AdtTypeDef := [])
    (fragment : UnsafeYulFragment) :
    compileStmt fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes
      (Stmt.unsafeYul fragment) = pure fragment.stmts := by
  simp [compileStmt, unsafeYulToEVMYul]

end Compiler.CompilationModel
