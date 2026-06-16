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
import Verity.Core.Intrinsics

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

def forEachSetBitBodyScope (inScopeNames : List String) (varName : String)
    (bitmap : Expr) (body : List Stmt) : List String :=
  let usedNames := varName :: (inScopeNames ++ collectExprNames bitmap ++ collectStmtListNames body)
  let bitmapName := pickFreshName "__forEach_bitmap" usedNames
  let bitName := pickFreshName "__forEach_bit" (bitmapName :: usedNames)
  bitName :: bitmapName :: varName :: inScopeNames

def forEachSetBitFallbackBodyScope (inScopeNames : List String) (varName : String)
    (bitmap : Expr) (body : List Stmt) : List String :=
  let usedNames := varName :: (inScopeNames ++ collectExprNames bitmap ++ collectStmtListNames body)
  let bitmapName := pickFreshName "__forEach_bitmap" usedNames
  let idxName := pickFreshName "__forEach_bit_idx" (bitmapName :: usedNames)
  idxName :: bitmapName :: varName :: inScopeNames

-- Compile statement to Yul (using mutual recursion for lists).
-- When isInternal=true, Stmt.return compiles to `__ret := value; leave` so internal
-- function execution terminates immediately without exiting the outer EVM call.
mutual
def compileStmtListWithFork (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := [])
    (adtTypes : List AdtTypeDef := [])
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (stmts : List Stmt) :
    Except String (List YulStmt) :=
  match stmts with
  | [] => pure []
  | s :: ss => do
      let head ← compileStmtWithFork fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes targetFork s
      let nextScopeNames := collectStmtNames s ++ inScopeNames
      let tail ← compileStmtListWithFork fields events errors dynamicSource internalRetNames isInternal nextScopeNames adtTypes targetFork ss
      pure (head ++ tail)

def compileStmtWithFork (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := [])
    (adtTypes : List AdtTypeDef := [])
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (stmt : Stmt) :
    Except String (List YulStmt) :=
  match stmt with
  | Stmt.letVar name value => do
      pure [YulStmt.let_ name (← compileExpr fields dynamicSource value)]
  | Stmt.assignVar name value => do
      pure [YulStmt.assign name (← compileExpr fields dynamicSource value)]
  | Stmt.setStorage field value =>
      match adtTypes with
      | [] => compileSetStorage fields dynamicSource field value
      | _ =>
          match value with
          | Expr.adtConstruct adtName variantName args =>
              compileAdtStorageWrite fields dynamicSource adtTypes field adtName variantName args
          | _ =>
              compileSetStorage fields dynamicSource field value
  | Stmt.setStorageAddr field value =>
      compileSetStorage fields dynamicSource field value true
  | Stmt.setStorageWord field wordOffset value =>
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) => do
          let valueExpr ← compileExpr fields dynamicSource value
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
      compileStorageArrayPush fields dynamicSource field value
  | Stmt.storageArrayPop field =>
      compileStorageArrayPop fields field
  | Stmt.setStorageArrayElement field index value =>
      compileSetStorageArrayElement fields dynamicSource field index value
  | Stmt.setMapping field key value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMapping"
  | Stmt.setMappingWord field key wordOffset value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMappingWord"
        wordOffset
  | Stmt.setMappingPackedWord field key wordOffset packed value => do
      compileMappingPackedSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        wordOffset
        packed
        "setMappingPackedWord"
  | Stmt.setMapping2 field key1 key2 value =>
      compileSetMapping2 fields dynamicSource field key1 key2 value
  | Stmt.setMapping2Word field key1 key2 wordOffset value =>
      compileSetMapping2Word fields dynamicSource field key1 key2 wordOffset value
  | Stmt.setMappingUint field key value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMappingUint"
  | Stmt.setMappingChain field keys value =>
      compileSetMappingChain fields dynamicSource field keys value
  | Stmt.setStructMember field key memberName value =>
      compileSetStructMember fields dynamicSource field key memberName value
  | Stmt.setStructMember2 field key1 key2 memberName value =>
      compileSetStructMember2 fields dynamicSource field key1 key2 memberName value
  | Stmt.require cond message =>
    do
      let failCond ← compileRequireFailCond fields dynamicSource cond
      pure [
        YulStmt.if_ failCond (revertWithMessage message)
      ]
  | Stmt.requireError cond errorName args => do
      let failCond ← compileRequireFailCond fields dynamicSource cond
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      let argExprs ← compileExprList fields dynamicSource args
      let revertStmts ← revertWithCustomError dynamicSource errorDef args argExprs
      pure [YulStmt.if_ failCond revertStmts]
  | Stmt.revertError errorName args => do
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      let argExprs ← compileExprList fields dynamicSource args
      revertWithCustomError dynamicSource errorDef args argExprs
  | Stmt.return value =>
    do
      let valueExpr ← compileExpr fields dynamicSource value
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
      let condExpr ← compileExpr fields dynamicSource cond
      let thenStmts ← compileStmtListWithFork fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes targetFork thenBranch
      let elseStmts ← compileStmtListWithFork fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes targetFork elseBranch
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
      let countExpr ← compileExpr fields dynamicSource count
      let forUsedNames := varName :: (inScopeNames ++ collectExprNames count ++ collectStmtListNames body)
      let idxName := pickFreshName "__forEach_idx" forUsedNames
      let countName := pickFreshName "__forEach_count" (idxName :: forUsedNames)
      -- Compile the body with the synthetic counters in scope (see `forEachBodyScope`),
      -- so a nested `forEach` cannot re-derive colliding `__forEach_idx`/`__forEach_count`.
      let bodyStmts ← compileStmtListWithFork fields events errors dynamicSource internalRetNames isInternal (forEachBodyScope inScopeNames varName count body) adtTypes targetFork body
      let initStmts := [
        YulStmt.let_ idxName (YulExpr.lit 0),
        YulStmt.let_ countName countExpr,
        YulStmt.let_ varName (YulExpr.lit 0)
      ]
      let condExpr := YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName]
      let postStmts := [YulStmt.assign idxName (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
      let bodyWithBind := YulStmt.assign varName (YulExpr.ident idxName) :: bodyStmts
      pure [YulStmt.for_ initStmts condExpr postStmts bodyWithBind]

  | Stmt.forEachSetBit varName bitmap body => do
      let bitmapExpr ← compileExpr fields dynamicSource bitmap
      let usedNames := varName :: (inScopeNames ++ collectExprNames bitmap ++ collectStmtListNames body)
      let bitmapName := pickFreshName "__forEach_bitmap" usedNames
      if Verity.Core.Intrinsics.HardFork.allows targetFork .osaka then
        let bitName := pickFreshName "__forEach_bit" (bitmapName :: usedNames)
        let bodyStmts ← compileStmtListWithFork fields events errors dynamicSource internalRetNames isInternal
          (forEachSetBitBodyScope inScopeNames varName bitmap body) adtTypes targetFork body
        let bitExpr := YulExpr.call "shl" [YulExpr.ident varName, YulExpr.lit 1]
        let clzExpr := YulExpr.call "verbatim_1i_1o"
          [YulExpr.verbatimHex "1e", YulExpr.ident bitmapName]
        let bindIndex := YulStmt.assign varName
          (YulExpr.call "sub" [YulExpr.lit 255, clzExpr])
        let bindBit := YulStmt.let_ bitName bitExpr
        let clearBit := YulStmt.assign bitmapName
          (YulExpr.call "and" [YulExpr.ident bitmapName, YulExpr.call "not" [YulExpr.ident bitName]])
        pure [YulStmt.block [
          YulStmt.let_ bitmapName bitmapExpr,
          YulStmt.let_ varName (YulExpr.lit 0),
          YulStmt.for_ [] (YulExpr.ident bitmapName) [] (bindIndex :: bindBit :: bodyStmts ++ [clearBit])
        ]]
      else
        let idxName := pickFreshName "__forEach_bit_idx" (bitmapName :: usedNames)
        let bodyStmts ← compileStmtListWithFork fields events errors dynamicSource internalRetNames isInternal
          (forEachSetBitFallbackBodyScope inScopeNames varName bitmap body) adtTypes targetFork body
        let bitExpr := YulExpr.call "shl" [YulExpr.ident idxName, YulExpr.lit 1]
        let hasBit := YulExpr.call "and" [YulExpr.ident bitmapName, bitExpr]
        pure [YulStmt.block [
          YulStmt.let_ bitmapName bitmapExpr,
          YulStmt.let_ varName (YulExpr.lit 0),
          YulStmt.for_
            [YulStmt.let_ idxName (YulExpr.lit 255)]
            (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.lit 256])
            [YulStmt.assign idxName (YulExpr.call "sub" [YulExpr.ident idxName, YulExpr.lit 1])]
            [YulStmt.if_ hasBit (YulStmt.assign varName (YulExpr.ident idxName) :: bodyStmts)]
        ]]

  | Stmt.unsafeBlock _ body => do
      -- Unsafe block: transparent wrapper, compile inner body directly (#1728, Axis 6 Step 6a)
      compileStmtListWithFork fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes targetFork body

  | Stmt.unsafeYul fragment =>
      pure (unsafeYulToEVMYul fragment)

  | Stmt.emit eventName args => do
      compileEmit fields events dynamicSource eventName args

  | Stmt.internalCall functionName args => do
      -- Internal function call as statement (#181)
      let argExprs ← compileExprList fields dynamicSource args
      pure [YulStmt.expr (YulExpr.call (internalFunctionYulName functionName) argExprs)]
  | Stmt.internalCallAssign names functionName args => do
      let argExprs ← compileExprList fields dynamicSource args
      pure [YulStmt.letMany names (YulExpr.call (internalFunctionYulName functionName) argExprs)]
  | Stmt.externalCallBind resultVars externalName args => do
      let argExprs ← compileExprList fields dynamicSource args
      if resultVars.isEmpty then
        pure [YulStmt.expr (YulExpr.call externalName argExprs)]
      else
        pure [YulStmt.letMany resultVars (YulExpr.call externalName argExprs)]
  -- Try-call variant: calls {externalName}_try which returns (success, result...)
  -- instead of reverting on failure. (#1727, Axis 1 Step 5f)
  | Stmt.tryExternalCallBind successVar resultVars externalName args => do
      let argExprs ← compileExprList fields dynamicSource args
      let tryFnName := s!"{externalName}_try"
      pure [YulStmt.letMany (successVar :: resultVars) (YulExpr.call tryFnName argExprs)]
  -- NOTE: safeTransfer, safeTransferFrom, externalCallWithReturn, callback, ecrecover
  -- have been removed. Use Stmt.ecm with the appropriate module from Compiler/Modules/.
  | Stmt.ecm mod args => do
      if args.length != mod.numArgs then
        throw s!"ECM '{mod.name}': expected {mod.numArgs} arguments, got {args.length}"
      let compiledArgs ← compileExprList fields dynamicSource args
      let ctx : ECM.CompilationContext := {
        isDynamicFromCalldata := dynamicSource == .calldata
      }
      mod.compile ctx compiledArgs
  | Stmt.returnValues values => do
      if isInternal then
        if values.length != internalRetNames.length then
          throw s!"Compilation error: internal return arity mismatch: expected {internalRetNames.length}, got {values.length}"
        else
          let compiled ← compileExprList fields dynamicSource values
          let assigns := (internalRetNames.zip compiled).map fun (name, valueExpr) =>
            YulStmt.assign name valueExpr
          pure (assigns ++ [YulStmt.leave])
      else if values.isEmpty then
        pure [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 0])]
      else
        let compiled ← compileExprList fields dynamicSource values
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
      let pointerExpr ← compileExpr fields dynamicSource pointer
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
        ← compileExpr fields dynamicSource offset,
        ← compileExpr fields dynamicSource value
      ])]
  | Stmt.tstore offset value => do
      pure [YulStmt.expr (YulExpr.call "tstore" [
        ← compileExpr fields dynamicSource offset,
        ← compileExpr fields dynamicSource value
      ])]
  | Stmt.calldatacopy destOffset sourceOffset size => do
      pure [YulStmt.expr (YulExpr.call "calldatacopy" [
        ← compileExpr fields dynamicSource destOffset,
        ← compileExpr fields dynamicSource sourceOffset,
        ← compileExpr fields dynamicSource size
      ])]
  | Stmt.returndataCopy destOffset sourceOffset size => do
      pure [YulStmt.expr (YulExpr.call "returndatacopy" [
        ← compileExpr fields dynamicSource destOffset,
        ← compileExpr fields dynamicSource sourceOffset,
        ← compileExpr fields dynamicSource size
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
      let topicExprs ← compileExprList fields dynamicSource topics
      let offsetExpr ← compileExpr fields dynamicSource dataOffset
      let sizeExpr ← compileExpr fields dynamicSource dataSize
      let logFn := s!"log{topics.length}"
      pure [YulStmt.expr (YulExpr.call logFn ([offsetExpr, sizeExpr] ++ topicExprs))]
  -- ADT pattern match: compile to YulStmt.switch on tag value (#1727 Steps 5c/5d)
  | Stmt.matchAdt adtName scrutinee branches => do
      let def_ ← lookupAdtTypeDef adtTypes adtName
      -- Compile the scrutinee (tag value expression)
      let scrutineeExpr ← compileExpr fields dynamicSource scrutinee
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
        inScopeNames adtTypes def_ baseSlot branches targetFork
      -- Default case: revert (should be unreachable for exhaustive matches)
      let defaultCase := [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
      pure [YulStmt.switch scrutineeExpr cases (some defaultCase)]

def compileMatchAdtBranches (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (dynamicSource : DynamicDataSource)
    (internalRetNames : List String) (isInternal : Bool)
    (inScopeNames : List String) (adtTypes : List AdtTypeDef)
    (def_ : AdtTypeDef) (baseSlot : Nat)
    (branches : List (String × List String × List Stmt))
    (targetFork : Verity.Core.Intrinsics.HardFork := .cancun) :
    Except String (List (Nat × List YulStmt)) :=
  match branches with
  | [] => pure []
  | (variantName, boundVarNames, body) :: rest => do
      let variant ← lookupAdtVariant def_ variantName
      if boundVarNames.length != variant.fields.length then
        throw s!"Compilation error: match branch '{variantName}' of ADT '{def_.name}' binds {boundVarNames.length} variables, but the variant has {variant.fields.length} fields"
      -- Bind each variable to sload(baseSlot + 1 + idx)
      let fieldBindings := boundVarNames.zipIdx.map fun (varName, idx) =>
        YulStmt.let_ varName (compileAdtFieldRead (YulExpr.lit baseSlot) idx)
      let bodyStmts ← compileStmtListWithFork fields events errors dynamicSource internalRetNames isInternal
        (boundVarNames.reverse ++ inScopeNames) adtTypes targetFork body
      let restCases ← compileMatchAdtBranches fields events errors dynamicSource internalRetNames isInternal
        inScopeNames adtTypes def_ baseSlot rest targetFork
      pure ((variant.tag, fieldBindings ++ bodyStmts) :: restCases)
end

def compileStmtList (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := [])
    (adtTypes : List AdtTypeDef := []) :
    List Stmt → Except String (List YulStmt) :=
  compileStmtListWithFork fields events errors dynamicSource internalRetNames isInternal
    inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun

def compileStmt (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := [])
    (adtTypes : List AdtTypeDef := []) :
    Stmt → Except String (List YulStmt) :=
  compileStmtWithFork fields events errors dynamicSource internalRetNames isInternal
    inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun

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
  simp [compileStmt, compileStmtWithFork, unsafeYulToEVMYul]

end Compiler.CompilationModel
