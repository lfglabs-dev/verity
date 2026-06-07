import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBodyClosure.Base

set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler
open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.YulGeneration
open Verity.Core.Free

/-!
## Universal safe-body closure

`BridgedSafeStmts` is the source-level whitelist used by the EVMYulLean native
lowering report: it collects the statement-list fragments that this module has
proved to compile into `BridgedStmts`. Internal helper calls and typed external
call binds are admitted through an explicit `BridgedFunctionTable` witness,
which proves the called Yul functions resolve to bridged bodies. Opaque ECM
statements remain outside this universal whitelist until concrete modules
provide bridgeable-output obligations.
-/

inductive BridgedSafeStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    Bool → List Stmt → Prop
  | externalRecursiveRawLog {stmts : List Stmt}
      (hStmts : BridgedSourceExternalRecursiveBodyWithRawLogStmts
        fields errors dynamicSource stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames false stmts
  | internalRecursiveRawLog {stmts : List Stmt}
      (hStmts : BridgedSourceInternalRecursiveBodyWithRawLogStmts
        fields errors dynamicSource stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames true stmts
  | storage {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStorageStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | storageAddr {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStorageAddrStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | require {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceRequireStmts fields dynamicSource stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | setStorageArrayElement {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceSetStorageArrayElementStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingChain {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingChainStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWrite {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWriteStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWriteMultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWriteMultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWrite2 {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWrite2Stmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWrite2MultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWrite2MultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMember {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMemberStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMember2 {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMember2Stmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMemberNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMemberNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMember2Nonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMember2NonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMemberMultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMemberMultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMember2MultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMember2MultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWord {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWordStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mapping2Word {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMapping2WordStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWordNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWordNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mapping2WordNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMapping2WordNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWordMultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWordMultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mapping2WordMultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMapping2WordMultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWordMultiSlotNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWordMultiSlotNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mapping2WordMultiSlotNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMapping2WordMultiSlotNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMemberMultiSlotNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMemberMultiSlotNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMember2MultiSlotNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMember2MultiSlotNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingPackedWord {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingPackedWordStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingPackedWordNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingPackedWordNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingPackedWordMultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingPackedWordMultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingPackedWordMultiSlotNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingPackedWordMultiSlotNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | returnValuesExternal {stmts : List Stmt}
      (hStmts : BridgedSourceReturnValuesExternalStmts stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames false stmts
  | returnValuesInternal {stmts : List Stmt}
      (hStmts : BridgedSourceReturnValuesInternalStmts internalRetNames stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames true stmts
  | mstore {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMstoreStmts stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | tstore {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceTstoreStmts stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | storageArrayPush {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStorageArrayPushStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | storageArrayPop {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStorageArrayPopStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | internalCall {isInternal : Bool} {stmts : List Stmt}
      {table : BridgedFunctionTable}
      (hStmts : BridgedSourceInternalCallStmts table stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | externalCallBind {isInternal : Bool} {stmts : List Stmt}
      {table : BridgedFunctionTable}
      (hStmts : BridgedSourceExternalCallBindStmts table stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | append {isInternal : Bool} {pfx sfx : List Stmt}
      (hPfx : BridgedSafeStmts fields errors dynamicSource internalRetNames
        isInternal pfx)
      (hSfx : BridgedSafeStmts fields errors dynamicSource internalRetNames
        isInternal sfx) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
        (pfx ++ sfx)

private theorem compileStmtList_append_eq
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) (adtTypes : List AdtTypeDef)
    (pfx sfx : List Stmt) :
    compileStmtList fields events errors dynamicSource internalRetNames isInternal
        inScopeNames adtTypes (pfx ++ sfx) =
      match
        compileStmtList fields events errors dynamicSource internalRetNames isInternal
          inScopeNames adtTypes pfx
      with
      | .error err => .error err
      | .ok pfxOut =>
          match
            compileStmtList fields events errors dynamicSource internalRetNames
              isInternal
              (List.foldl (fun scope stmt => collectStmtNames stmt ++ scope)
                inScopeNames pfx)
              adtTypes sfx
          with
          | .error err => .error err
          | .ok sfxOut => .ok (pfxOut ++ sfxOut) := by
  induction pfx generalizing inScopeNames with
  | nil =>
      simp [compileStmtList, Pure.pure, Except.pure]
      cases compileStmtList fields events errors dynamicSource internalRetNames
        isInternal inScopeNames adtTypes sfx <;> rfl
  | cons head tail ih =>
      simp only [List.cons_append, compileStmtList, bind, Except.bind]
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames adtTypes head with
      | error err =>
          simp [hHead]
      | ok headOut =>
          simp [hHead]
          rw [ih (collectStmtNames head ++ inScopeNames)]
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames)
              adtTypes tail with
          | error err =>
              simp [hTail]
          | ok tailOut =>
              simp [hTail]
              cases hSfx : compileStmtList fields events errors dynamicSource
                  internalRetNames isInternal
                  ((List.map collectStmtNames tail).reverse.flatten ++
                    (collectStmtNames head ++ inScopeNames))
                  adtTypes sfx with
              | error err =>
                  simp [hSfx, Pure.pure, Except.pure]
              | ok sfxOut =>
                  simp [hSfx, List.append_assoc, Pure.pure, Except.pure]

/-- The singleton `mstore` shape exposed by `SupportedFragment.mstoreSingle`
    is a native safe body whenever its offset and value are compile-core
    expressions. -/
theorem bridgedSafeStmts_mstoreSingle_of_exprCompileCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {offset value : Expr}
    (hOffset : _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore offset)
    (hValue : _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore value) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.mstore offset value] :=
  BridgedSafeStmts.mstore (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact bridgedSourceMstoreStmt_of_exprCompileCore hOffset hValue)

/-- The singleton `setStorage` shape exposed by
    `SupportedFragment.setStorageSingleSlot` is a native safe body whenever its
    value is a compile-core expression and the field is an unpacked uint slot. -/
theorem bridgedSafeStmts_setStorageSingleSlot_of_exprCompileCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {fieldName : String} {value : Expr} {slot : Nat}
    (hValue : _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore value)
    (hFind :
      findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setStorage fieldName value] :=
  BridgedSafeStmts.storage (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact bridgedSourceStorageStmt_setStorageSingleSlot_of_exprCompileCore
      hValue hFind)

/-- The singleton `setStorageAddr` shape exposed by
    `SupportedFragment.setStorageAddrSingleSlot` is a native safe body whenever
    its value is a compile-core expression and the field is an unpacked address
    slot. -/
theorem bridgedSafeStmts_setStorageAddrSingleSlot_of_exprCompileCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {fieldName : String} {value : Expr} {slot : Nat}
    (hValue : _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore value)
    (hFind :
      findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.address }, slot)) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setStorageAddr fieldName value] :=
  BridgedSafeStmts.storageAddr (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact bridgedSourceStorageAddrStmt_setStorageAddrSingleSlot_of_exprCompileCore
      hValue hFind)

/-- A singleton `require` whose condition is compile-core is a native safe
    body. -/
theorem bridgedSafeStmts_requireSingle_of_exprCompileCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {cond : Expr} {message : String}
    (hCond : _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore cond) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.require cond message] :=
  BridgedSafeStmts.require (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact bridgedSourceRequireStmt_of_exprCompileCore hCond)

/-- A singleton literal guard-family clause is a native safe body. -/
theorem bridgedSafeStmts_requireGuardFamilyClause
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool}
    (clause : RequireLiteralGuardFamilyClause) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [clause.toStmt] :=
  BridgedSafeStmts.require (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact bridgedSourceRequireStmt_of_guardFamilyClause clause)

/-- A `let` binding whose RHS is syntactic `keccak256(offset, size)` is a
    native pure-binding source statement when the offset and size arguments are
    compile-core expressions. This deliberately stays outside
    `StmtListCompileCore`, whose source/IR semantic theorem still excludes
    memory-slice hashing. -/
theorem bridgedSourcePureBindingStmt_letKeccak_of_exprCompileCore
    {name : String} {offset size : Expr}
    (hOffset :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore offset)
    (hSize :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore size) :
    BridgedSourcePureBindingStmt
      (.letVar name (.keccak256 offset size)) :=
  BridgedSourcePureBindingStmt.letVar name (.keccak256 offset size)
    (bridgedSourceExpr_keccak256_of_exprCompileCore hOffset hSize)

/-- An assignment whose RHS is syntactic `keccak256(offset, size)` is a native
    pure-binding source statement when the offset and size arguments are
    compile-core expressions. -/
theorem bridgedSourcePureBindingStmt_assignKeccak_of_exprCompileCore
    {name : String} {offset size : Expr}
    (hOffset :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore offset)
    (hSize :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore size) :
    BridgedSourcePureBindingStmt
      (.assignVar name (.keccak256 offset size)) :=
  BridgedSourcePureBindingStmt.assignVar name (.keccak256 offset size)
    (bridgedSourceExpr_keccak256_of_exprCompileCore hOffset hSize)

/-- Singleton native safe-body package for `let name := keccak256(offset,size)`
    with compile-core offset and size arguments. -/
theorem bridgedSafeStmts_letKeccak_of_exprCompileCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {name : String} {offset size : Expr}
    (hOffset :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore offset)
    (hSize :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore size) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.letVar name (.keccak256 offset size)] :=
  BridgedSafeStmts.storage (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceStorageStmt.pureBinding
      (bridgedSourcePureBindingStmt_letKeccak_of_exprCompileCore hOffset hSize))

/-- Singleton native safe-body package for `name := keccak256(offset,size)`
    with compile-core offset and size arguments. -/
theorem bridgedSafeStmts_assignKeccak_of_exprCompileCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {name : String} {offset size : Expr}
    (hOffset :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore offset)
    (hSize :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore size) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.assignVar name (.keccak256 offset size)] :=
  BridgedSafeStmts.storage (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceStorageStmt.pureBinding
      (bridgedSourcePureBindingStmt_assignKeccak_of_exprCompileCore hOffset hSize))

private def bridgedExternalRawLogLetVar
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {name : String} {value : Expr}
    (hValue :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore value) :
    BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
      dynamicSource (.letVar name value) :=
  .base (.base (.base (.storage (.pureBinding
    (.letVar _ _ (bridgedSourceExpr_of_exprCompileCore hValue))))))

private def bridgedExternalRawLogLetKeccak
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {name : String} {offset size : Expr}
    (hOffset :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore offset)
    (hSize :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore size) :
    BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
      dynamicSource (.letVar name (.keccak256 offset size)) :=
  .base (.base (.base (.storage (.pureBinding
    (bridgedSourcePureBindingStmt_letKeccak_of_exprCompileCore hOffset hSize)))))

private def bridgedExternalRawLogAssignVar
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {name : String} {value : Expr}
    (hValue :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore value) :
    BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
      dynamicSource (.assignVar name value) :=
  .base (.base (.base (.storage (.pureBinding
    (.assignVar _ _ (bridgedSourceExpr_of_exprCompileCore hValue))))))

private def bridgedExternalRawLogRequire
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {cond : Expr} {message : String}
    (hCond :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore cond) :
    BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
      dynamicSource (.require cond message) :=
  .base (.base (.base (.require
    (bridgedSourceRequireStmt_of_exprCompileCore hCond))))

private def bridgedExternalRawLogReturn
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {value : Expr}
    (hValue :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore value) :
    BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
      dynamicSource (.return value) :=
  .base (.base (.base (.terminator
    (.returnExternal _ (bridgedSourceExpr_of_exprCompileCore hValue)))))

private def bridgedExternalRawLogStop
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} :
    BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
      dynamicSource .stop :=
  .base (.base (.base (.terminator .stop)))

private def bridgedExternalRawLogMstore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {offset value : Expr}
    (hOffset :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore offset)
    (hValue :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore value) :
    BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
      dynamicSource (.mstore offset value) :=
  .base (.base (.memoryWrite
    (.mstore _ _ (bridgedSourceExpr_of_exprCompileCore hOffset)
      (bridgedSourceExpr_of_exprCompileCore hValue))))

private def bridgedExternalRawLogTstore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {offset value : Expr}
    (hOffset :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore offset)
    (hValue :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore value) :
    BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
      dynamicSource (.tstore offset value) :=
  .base (.base (.memoryWrite
    (.tstore _ _ (bridgedSourceExpr_of_exprCompileCore hOffset)
      (bridgedSourceExpr_of_exprCompileCore hValue))))

private def bridgedExternalRawLogIte
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource}
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hCond :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore cond)
    (hThen :
      BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
        dynamicSource thenBranch)
    (hElse :
      BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
        dynamicSource elseBranch) :
    BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
      dynamicSource (.ite cond thenBranch elseBranch) :=
  .ite _ _ _ (bridgedSourceExpr_of_exprCompileCore hCond) hThen hElse

/-- Source compile-core statement lists are covered by the recursive external
    raw-log fragment: pure bindings route through the storage/body base
    predicate, requires and terminators are direct body cases, and direct
    memory/transient writes route through the memory-write extension. -/
theorem bridgedSourceExternalRecursiveBodyWithRawLogStmts_of_stmtListCompileCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {scope : List String}
    {stmts : List Stmt}
    (hCore : _root_.Compiler.Proofs.IRGeneration.FunctionBody.StmtListCompileCore
      scope stmts) :
    BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
      dynamicSource stmts := by
  induction hCore with
  | nil =>
      exact .nil
  | letVar hValue _hScope _hRest ih =>
      exact .cons (bridgedExternalRawLogLetVar hValue) ih
  | assignVar hValue _hScope _hRest ih =>
      exact .cons (bridgedExternalRawLogAssignVar hValue) ih
  | require_ hCond _hScope _hRest ih =>
      exact .cons (bridgedExternalRawLogRequire hCond) ih
  | return_ hValue _hScope _hRest ih =>
      exact .cons (bridgedExternalRawLogReturn hValue) ih
  | stop _hRest ih =>
      exact .cons bridgedExternalRawLogStop ih
  | mstore hOffset _hOffsetScope hValue _hValueScope _hRest ih =>
      exact .cons (bridgedExternalRawLogMstore hOffset hValue) ih
  | tstore hOffset _hOffsetScope hValue _hValueScope _hRest ih =>
      exact .cons (bridgedExternalRawLogTstore hOffset hValue) ih

/-- Terminal compile-core statement lists have the same external native source
    coverage as ordinary compile-core lists. The terminal `return`/`stop` cases
    delegate their tails to the compile-core bridge exposed by the terminal
    grammar. -/
theorem bridgedSourceExternalRecursiveBodyWithRawLogStmts_of_stmtListTerminalCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {scope : List String}
    {stmts : List Stmt}
    (hTerminal :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.StmtListTerminalCore
        scope stmts) :
    BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
      dynamicSource stmts := by
  induction hTerminal with
  | letVar hValue _hScope _hRest ih =>
      exact .cons (bridgedExternalRawLogLetVar hValue) ih
  | assignVar hValue _hScope _hRest ih =>
      exact .cons (bridgedExternalRawLogAssignVar hValue) ih
  | require_ hCond _hScope _hRest ih =>
      exact .cons (bridgedExternalRawLogRequire hCond) ih
  | return_ hValue _hScope hRest =>
      exact .cons (bridgedExternalRawLogReturn hValue)
        (bridgedSourceExternalRecursiveBodyWithRawLogStmts_of_stmtListCompileCore
          hRest)
  | stop hRest =>
      exact .cons bridgedExternalRawLogStop
        (bridgedSourceExternalRecursiveBodyWithRawLogStmts_of_stmtListCompileCore
          hRest)
  | mstore hOffset _hOffsetScope hValue _hValueScope _hRest ih =>
      exact .cons (bridgedExternalRawLogMstore hOffset hValue) ih
  | tstore hOffset _hOffsetScope hValue _hValueScope _hRest ih =>
      exact .cons (bridgedExternalRawLogTstore hOffset hValue) ih
  | ite hCond _hScope hThen hElse hRest ihThen ihElse =>
      exact .cons (bridgedExternalRawLogIte hCond ihThen ihElse)
        (bridgedSourceExternalRecursiveBodyWithRawLogStmts_of_stmtListCompileCore
          hRest)

/-- External source bodies accepted by the compile-core grammar are native safe
    bodies, so callers do not need to manually rebuild the raw-log recursive
    source predicate. -/
theorem bridgedSafeStmts_externalCompileCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {scope : List String} {stmts : List Stmt}
    (hCore :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.StmtListCompileCore
        scope stmts) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames false stmts :=
  BridgedSafeStmts.externalRecursiveRawLog
    (bridgedSourceExternalRecursiveBodyWithRawLogStmts_of_stmtListCompileCore
      hCore)

/-- External source bodies accepted by the terminal-core grammar are native safe
    bodies. -/
theorem bridgedSafeStmts_externalTerminalCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {scope : List String} {stmts : List Stmt}
    (hTerminal :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.StmtListTerminalCore
        scope stmts) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames false stmts :=
  BridgedSafeStmts.externalRecursiveRawLog
    (bridgedSourceExternalRecursiveBodyWithRawLogStmts_of_stmtListTerminalCore
      hTerminal)

/-- External native safe-body package for the common single-word memory
    preimage shape:

    `mstore(storeOffset, storeValue); let name := keccak256(hashOffset, hashSize)`.

    This is still only a native syntactic Yul-closure fact; the corresponding
    source-level memory-slice hash semantics remain outside `StmtListCompileCore`. -/
theorem bridgedSafeStmts_externalMstoreLetKeccak_of_exprCompileCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {storeOffset storeValue hashOffset hashSize : Expr} {name : String}
    (hStoreOffset :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore storeOffset)
    (hStoreValue :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore storeValue)
    (hHashOffset :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore hashOffset)
    (hHashSize :
      _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore hashSize) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames false
      [Stmt.mstore storeOffset storeValue,
        Stmt.letVar name (.keccak256 hashOffset hashSize)] :=
  BridgedSafeStmts.externalRecursiveRawLog
    (.cons
      (bridgedExternalRawLogMstore hStoreOffset hStoreValue)
      (.cons
        (bridgedExternalRawLogLetKeccak hHashOffset hHashSize)
        .nil))

/-- The singleton `tstore` shape exposed by `SupportedFragment.tstoreSingle`
    is a native safe body whenever its offset and value are compile-core
    expressions. -/
theorem bridgedSafeStmts_tstoreSingle_of_exprCompileCore
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {offset value : Expr}
    (hOffset : _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore offset)
    (hValue : _root_.Compiler.Proofs.IRGeneration.FunctionBody.ExprCompileCore value) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.tstore offset value] :=
  BridgedSafeStmts.tstore (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact bridgedSourceTstoreStmt_of_exprCompileCore hOffset hValue)

/-- Singleton native safe-body package for a single-slot `setMapping` write. -/
theorem bridgedSafeStmts_setMappingSingleSlot
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat} {key value : Expr}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setMapping field key value] :=
  BridgedSafeStmts.mappingWrite (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceMappingWriteStmt.setMapping field hKey hValue
      hMapping hSlots)

/-- Singleton native safe-body package for a single-slot `setMappingUint`
write. -/
theorem bridgedSafeStmts_setMappingUintSingleSlot
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat} {key value : Expr}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setMappingUint field key value] :=
  BridgedSafeStmts.mappingWrite (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceMappingWriteStmt.setMappingUint field hKey hValue
      hMapping hSlots)

/-- Singleton native safe-body package for a single-slot `setMappingChain`
    write. -/
theorem bridgedSafeStmts_setMappingChainSingleSlot
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat}
    {keys : List Expr} {value : Expr}
    (hKeys : ∀ key ∈ keys, BridgedSourceExpr key)
    (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setMappingChain field keys value] :=
  BridgedSafeStmts.mappingChain (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceMappingChainStmt.setMappingChain field hKeys hValue
      hMapping hSlots)

/-- Singleton native safe-body package for a single-slot `setMapping2` write. -/
theorem bridgedSafeStmts_setMapping2SingleSlot
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat}
    {key1 key2 value : Expr}
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setMapping2 field key1 key2 value] :=
  BridgedSafeStmts.mappingWrite2 (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceMappingWrite2Stmt.setMapping2 field hKey1 hKey2
      hValue hMapping2 hSlots)

/-- Singleton native safe-body package for a single-slot, wordOffset=0
    `setMappingWord` write. -/
theorem bridgedSafeStmts_setMappingWordSingleSlot
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat}
    {key value : Expr} {wordOffset : Nat}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hWordOffset : wordOffset = 0) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setMappingWord field key wordOffset value] :=
  BridgedSafeStmts.mappingWord (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceMappingWordStmt.setMappingWord field wordOffset
      hKey hValue hMapping hSlots hWordOffset)

/-- Singleton native safe-body package for a single-slot, wordOffset=0
    `setMapping2Word` write. -/
theorem bridgedSafeStmts_setMapping2WordSingleSlot
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat}
    {key1 key2 value : Expr} {wordOffset : Nat}
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hWordOffset : wordOffset = 0) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setMapping2Word field key1 key2 wordOffset value] :=
  BridgedSafeStmts.mapping2Word (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceMapping2WordStmt.setMapping2Word field wordOffset
      hKey1 hKey2 hValue hMapping2 hSlots hWordOffset)

/-- Singleton native safe-body package for a single-slot, wordOffset≠0
    `setMappingWord` write. -/
theorem bridgedSafeStmts_setMappingWordSingleSlotNonzero
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot wordOffset : Nat}
    {key value : Expr}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hNonzero : wordOffset ≠ 0) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setMappingWord field key wordOffset value] :=
  BridgedSafeStmts.mappingWordNonzero (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceMappingWordNonzeroStmt.setMappingWord field
      hKey hValue hMapping hSlots hNonzero)

/-- Singleton native safe-body package for a single-slot, wordOffset≠0
    `setMapping2Word` write. -/
theorem bridgedSafeStmts_setMapping2WordSingleSlotNonzero
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot wordOffset : Nat}
    {key1 key2 value : Expr}
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hNonzero : wordOffset ≠ 0) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setMapping2Word field key1 key2 wordOffset value] :=
  BridgedSafeStmts.mapping2WordNonzero (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceMapping2WordNonzeroStmt.setMapping2Word field
      hKey1 hKey2 hValue hMapping2 hSlots hNonzero)

/-- Singleton native safe-body package for a single-slot, wordOffset=0
    `setMappingPackedWord` write. -/
theorem bridgedSafeStmts_setMappingPackedWordSingleSlot
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat}
    {key value : Expr} {wordOffset : Nat} {packed : PackedBits}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hWordOffset : wordOffset = 0)
    (hPacked : packedBitsValid packed = true) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setMappingPackedWord field key wordOffset packed value] :=
  BridgedSafeStmts.mappingPackedWord (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceMappingPackedWordStmt.setMappingPackedWord field
      wordOffset packed hKey hValue hMapping hSlots hWordOffset hPacked)

/-- Singleton native safe-body package for a single-slot, wordOffset=0
    `setStructMember` write. -/
theorem bridgedSafeStmts_setStructMemberSingleSlot
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat}
    {key value : Expr} {memberName : String}
    {members : List StructMember} {member : StructMember}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hNotMapping2 : isMapping2 fields field = false)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hWordOffset : member.wordOffset = 0)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setStructMember field key memberName value] :=
  BridgedSafeStmts.structMember (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceStructMemberStmt.setStructMember field memberName
      members member hKey hValue hNotMapping2 hMembers hFindMember hUnpacked
      hWordOffset hMapping hSlots)

/-- Singleton native safe-body package for a single-slot, wordOffset=0
    `setStructMember2` write. -/
theorem bridgedSafeStmts_setStructMember2SingleSlot
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat}
    {key1 key2 value : Expr} {memberName : String}
    {members : List StructMember} {member : StructMember}
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hWordOffset : member.wordOffset = 0)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setStructMember2 field key1 key2 memberName value] :=
  BridgedSafeStmts.structMember2 (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceStructMember2Stmt.setStructMember2 field memberName
      members member hKey1 hKey2 hValue hMapping2 hMembers hFindMember
      hUnpacked hWordOffset hSlots)

/-- Singleton native safe-body package for a single-slot, wordOffset≠0
    `setStructMember` write. -/
theorem bridgedSafeStmts_setStructMemberSingleSlotNonzero
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat}
    {key value : Expr} {memberName : String}
    {members : List StructMember} {member : StructMember}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hNotMapping2 : isMapping2 fields field = false)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hNonzero : member.wordOffset ≠ 0)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setStructMember field key memberName value] :=
  BridgedSafeStmts.structMemberNonzero (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceStructMemberNonzeroStmt.setStructMember field memberName
      members member hKey hValue hNotMapping2 hMembers hFindMember hUnpacked
      hNonzero hMapping hSlots)

/-- Singleton native safe-body package for a single-slot, wordOffset≠0
    `setStructMember2` write. -/
theorem bridgedSafeStmts_setStructMember2SingleSlotNonzero
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {field : String} {slot : Nat}
    {key1 key2 value : Expr} {memberName : String}
    {members : List StructMember} {member : StructMember}
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hNonzero : member.wordOffset ≠ 0)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal
      [Stmt.setStructMember2 field key1 key2 memberName value] :=
  BridgedSafeStmts.structMember2Nonzero (by
    intro stmt hMem
    simp only [List.mem_singleton] at hMem
    subst stmt
    exact BridgedSourceStructMember2NonzeroStmt.setStructMember2 field
      memberName members member hKey1 hKey2 hValue hMapping2 hMembers
      hFindMember hUnpacked hNonzero hSlots)

/-- Every source statement list accepted by `BridgedSafeStmts` compiles to a
Yul statement list accepted by `BridgedStmts`. This is the B7 aggregation
theorem: callers use one whitelist witness instead of choosing a fragment-
specific closure lemma manually. -/
theorem compileStmtList_always_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSafeStmts fields errors dynamicSource internalRetNames
        isInternal stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        BridgedStmts out := by
  intro stmts inScopeNames hSafe out hOk
  induction hSafe generalizing inScopeNames out with
  | externalRecursiveRawLog hStmts =>
      exact compileStmtList_external_recursive_body_with_raw_log_bridged fields
        events errors dynamicSource internalRetNames hStmts inScopeNames hOk
  | internalRecursiveRawLog hStmts =>
      exact compileStmtList_internal_recursive_body_with_raw_log_bridged fields
        events errors dynamicSource internalRetNames hStmts inScopeNames hOk
  | storage hStmts =>
      exact compileStmtList_storage_fragment_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | storageAddr hStmts =>
      exact compileStmtList_storageAddr_bridged fields events errors dynamicSource
        internalRetNames _ _ inScopeNames hStmts hOk
  | require hStmts =>
      exact compileStmtList_require_bridged fields events errors dynamicSource
        internalRetNames _ _ inScopeNames hStmts hOk
  | setStorageArrayElement hStmts =>
      exact compileStmtList_setStorageArrayElement_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingChain hStmts =>
      exact compileStmtList_mappingChain_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWrite hStmts =>
      exact compileStmtList_mappingWrite_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWriteMultiSlot hStmts =>
      exact compileStmtList_mappingWriteMultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWrite2 hStmts =>
      exact compileStmtList_mappingWrite2_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWrite2MultiSlot hStmts =>
      exact compileStmtList_mappingWrite2MultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMember hStmts =>
      exact compileStmtList_structMember_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMember2 hStmts =>
      exact compileStmtList_structMember2_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMemberNonzero hStmts =>
      exact compileStmtList_structMemberNonzero_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMember2Nonzero hStmts =>
      exact compileStmtList_structMember2Nonzero_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMemberMultiSlot hStmts =>
      exact compileStmtList_structMemberMultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMember2MultiSlot hStmts =>
      exact compileStmtList_structMember2MultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWord hStmts =>
      exact compileStmtList_mappingWord_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mapping2Word hStmts =>
      exact compileStmtList_mapping2Word_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWordNonzero hStmts =>
      exact compileStmtList_mappingWordNonzero_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mapping2WordNonzero hStmts =>
      exact compileStmtList_mapping2WordNonzero_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWordMultiSlot hStmts =>
      exact compileStmtList_mappingWordMultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mapping2WordMultiSlot hStmts =>
      exact compileStmtList_mapping2WordMultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWordMultiSlotNonzero hStmts =>
      exact compileStmtList_mappingWordMultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames _ _ inScopeNames
        hStmts hOk
  | mapping2WordMultiSlotNonzero hStmts =>
      exact compileStmtList_mapping2WordMultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames _ _ inScopeNames
        hStmts hOk
  | structMemberMultiSlotNonzero hStmts =>
      exact compileStmtList_structMemberMultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames _ _ inScopeNames
        hStmts hOk
  | structMember2MultiSlotNonzero hStmts =>
      exact compileStmtList_structMember2MultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames _ _ inScopeNames
        hStmts hOk
  | mappingPackedWord hStmts =>
      exact compileStmtList_mappingPackedWord_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingPackedWordNonzero hStmts =>
      exact compileStmtList_mappingPackedWordNonzero_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingPackedWordMultiSlot hStmts =>
      exact compileStmtList_mappingPackedWordMultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingPackedWordMultiSlotNonzero hStmts =>
      exact compileStmtList_mappingPackedWordMultiSlotNonzero_bridged fields
        events errors dynamicSource internalRetNames _ _ inScopeNames
        hStmts hOk
  | returnValuesExternal hStmts =>
      exact compileStmtList_returnValuesExternal_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames hStmts hOk
  | returnValuesInternal hStmts =>
      exact compileStmtList_returnValuesInternal_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames hStmts hOk
  | mstore hStmts =>
      exact compileStmtList_mstore_bridged fields events errors dynamicSource
        internalRetNames _ _ inScopeNames hStmts hOk
  | tstore hStmts =>
      exact compileStmtList_tstore_bridged fields events errors dynamicSource
        internalRetNames _ _ inScopeNames hStmts hOk
  | storageArrayPush hStmts =>
      exact compileStmtList_storageArrayPush_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | storageArrayPop hStmts =>
      exact compileStmtList_storageArrayPop_bridged fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | internalCall hStmts =>
      exact compileStmtList_internalCall_bridged fields events errors
        dynamicSource internalRetNames _ [] _ hStmts inScopeNames hOk
  | externalCallBind hStmts =>
      exact compileStmtList_externalCallBind_bridged fields events errors
        dynamicSource internalRetNames _ [] _ hStmts inScopeNames hOk
  | append hPfx hSfx ihPfx ihSfx =>
      rename_i localIsInternal pfx sfx
      rw [compileStmtList_append_eq fields events errors dynamicSource
        internalRetNames localIsInternal inScopeNames [] pfx sfx] at hOk
      cases hPfxCompile : compileStmtList fields events errors dynamicSource
          internalRetNames localIsInternal inScopeNames [] pfx with
      | error err =>
          simp [hPfxCompile] at hOk
      | ok pfxOut =>
          simp [hPfxCompile] at hOk
          cases hSfxCompile : compileStmtList fields events errors dynamicSource
              internalRetNames localIsInternal
              ((List.map collectStmtNames pfx).reverse.flatten ++ inScopeNames)
              [] sfx with
          | error err =>
              simp [hSfxCompile] at hOk
          | ok sfxOut =>
              simp [hSfxCompile, Pure.pure, Except.pure] at hOk
              subst out
              exact BridgedStmts_append
                (ihPfx inScopeNames hPfxCompile)
                (ihSfx
                  ((List.map collectStmtNames pfx).reverse.flatten ++
                    inScopeNames)
                  hSfxCompile)

theorem compileStmtList_always_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSafeStmts fields errors dynamicSource internalRetNames
        isInternal stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmts inScopeNames hSafe out hOk
  induction hSafe generalizing inScopeNames out with
  | externalRecursiveRawLog hStmts =>
      exact compileStmtList_external_recursive_body_with_raw_log_noFuncDefs
        fields events errors dynamicSource internalRetNames hStmts inScopeNames hOk
  | internalRecursiveRawLog hStmts =>
      exact compileStmtList_internal_recursive_body_with_raw_log_noFuncDefs
        fields events errors dynamicSource internalRetNames hStmts inScopeNames hOk
  | storage hStmts =>
      exact compileStmtList_storage_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | storageAddr hStmts =>
      exact compileStmtList_storageAddr_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | require hStmts =>
      exact compileStmtList_require_noFuncDefs fields events errors dynamicSource
        internalRetNames _ _ inScopeNames hStmts hOk
  | setStorageArrayElement hStmts =>
      exact compileStmtList_setStorageArrayElement_noFuncDefs fields events
        errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingChain hStmts =>
      exact compileStmtList_mappingChain_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWrite hStmts =>
      exact compileStmtList_mappingWrite_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWriteMultiSlot hStmts =>
      exact compileStmtList_mappingWriteMultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWrite2 hStmts =>
      exact compileStmtList_mappingWrite2_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWrite2MultiSlot hStmts =>
      exact compileStmtList_mappingWrite2MultiSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMember hStmts =>
      exact compileStmtList_structMember_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMember2 hStmts =>
      exact compileStmtList_structMember2_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMemberNonzero hStmts =>
      exact compileStmtList_structMemberNonzero_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMember2Nonzero hStmts =>
      exact compileStmtList_structMember2Nonzero_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMemberMultiSlot hStmts =>
      exact compileStmtList_structMemberMultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMember2MultiSlot hStmts =>
      exact compileStmtList_structMember2MultiSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWord hStmts =>
      exact compileStmtList_mappingWord_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mapping2Word hStmts =>
      exact compileStmtList_mapping2Word_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWordNonzero hStmts =>
      exact compileStmtList_mappingWordNonzero_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mapping2WordNonzero hStmts =>
      exact compileStmtList_mapping2WordNonzero_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWordMultiSlot hStmts =>
      exact compileStmtList_mappingWordMultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mapping2WordMultiSlot hStmts =>
      exact compileStmtList_mapping2WordMultiSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingWordMultiSlotNonzero hStmts =>
      exact compileStmtList_mappingWordMultiSlotNonzero_noFuncDefs fields events
        errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mapping2WordMultiSlotNonzero hStmts =>
      exact compileStmtList_mapping2WordMultiSlotNonzero_noFuncDefs fields
        events errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMemberMultiSlotNonzero hStmts =>
      exact compileStmtList_structMemberMultiSlotNonzero_noFuncDefs fields
        events errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | structMember2MultiSlotNonzero hStmts =>
      exact compileStmtList_structMember2MultiSlotNonzero_noFuncDefs fields
        events errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingPackedWord hStmts =>
      exact compileStmtList_mappingPackedWord_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingPackedWordNonzero hStmts =>
      exact compileStmtList_mappingPackedWordNonzero_noFuncDefs fields events
        errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingPackedWordMultiSlot hStmts =>
      exact compileStmtList_mappingPackedWordMultiSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | mappingPackedWordMultiSlotNonzero hStmts =>
      exact compileStmtList_mappingPackedWordMultiSlotNonzero_noFuncDefs fields
        events errors dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | returnValuesExternal hStmts =>
      exact compileStmtList_returnValuesExternal_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames hStmts hOk
  | returnValuesInternal hStmts =>
      exact compileStmtList_returnValuesInternal_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames hStmts hOk
  | mstore hStmts =>
      exact compileStmtList_mstore_noFuncDefs fields events errors dynamicSource
        internalRetNames _ _ inScopeNames hStmts hOk
  | tstore hStmts =>
      exact compileStmtList_tstore_noFuncDefs fields events errors dynamicSource
        internalRetNames _ _ inScopeNames hStmts hOk
  | storageArrayPush hStmts =>
      exact compileStmtList_storageArrayPush_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | storageArrayPop hStmts =>
      exact compileStmtList_storageArrayPop_noFuncDefs fields events errors
        dynamicSource internalRetNames _ _ inScopeNames hStmts hOk
  | internalCall hStmts =>
      exact compileStmtList_internalCall_noFuncDefs fields events errors
        dynamicSource internalRetNames _ [] _ hStmts inScopeNames hOk
  | externalCallBind hStmts =>
      exact compileStmtList_externalCallBind_noFuncDefs fields events errors
        dynamicSource internalRetNames _ [] _ hStmts inScopeNames hOk
  | append hPfx hSfx ihPfx ihSfx =>
      rename_i localIsInternal pfx sfx
      rw [compileStmtList_append_eq fields events errors dynamicSource
        internalRetNames localIsInternal inScopeNames [] pfx sfx] at hOk
      cases hPfxCompile : compileStmtList fields events errors dynamicSource
          internalRetNames localIsInternal inScopeNames [] pfx with
      | error err =>
          simp [hPfxCompile] at hOk
      | ok pfxOut =>
          simp [hPfxCompile] at hOk
          cases hSfxCompile : compileStmtList fields events errors dynamicSource
              internalRetNames localIsInternal
              ((List.map collectStmtNames pfx).reverse.flatten ++ inScopeNames)
              [] sfx with
          | error err =>
              simp [hSfxCompile] at hOk
          | ok sfxOut =>
              simp [hSfxCompile, Pure.pure, Except.pure] at hOk
              subst out
              rw [Native.yulStmtsContainFuncDef_append]
              simp [ihPfx inScopeNames hPfxCompile,
                ihSfx
                  ((List.map collectStmtNames pfx).reverse.flatten ++
                    inScopeNames)
                  hSfxCompile]

end Compiler.Proofs.YulGeneration.Backends
