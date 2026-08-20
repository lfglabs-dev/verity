/-
  Per-statement generic whitelist for the EVMYulLean native safe-body closure.

  `BridgedSourceStmt` is the per-statement union of the fragment whitelists
  that `Base.lean` proves compile into `BridgedStmts`. It replaces the
  list-level fragment multiplexing of `BridgedSafeStmts` (in `Safe.lean`)
  with a single statement-indexed inductive: a statement list is safe exactly
  when every member statement is `BridgedSourceStmt`.

  The master closure theorems `compileStmt_bridgedSource_bridged` /
  `compileStmt_bridgedSource_noFuncDefs` dispatch each constructor to the
  existing fragment-specific statement-level closure lemma, and the list-level
  wrappers lift them pointwise. `Safe.lean` re-derives its B7 aggregation
  theorems (`compileStmtList_always_bridged` / `compileStmtList_always_noFuncDefs`)
  from these, so downstream consumers are untouched.

  Run: lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBodyClosure.Generic
-/

import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBodyClosure.Base

set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler
open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.YulGeneration
open Verity.Core.Free

private theorem compileStmtWithFork_cancun_eq_compileStmt
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (stmt : Stmt)
    (internalFunctions : List FunctionSpec := []) :
    compileStmtWithFork fields events errors dynamicSource internalRetNames isInternal
      inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun stmt internalFunctions =
    compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames adtTypes stmt internalFunctions := rfl

private theorem compileStmtListWithFork_cancun_eq_compileStmtList
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (stmts : List Stmt)
    (internalFunctions : List FunctionSpec := []) :
    compileStmtListWithFork fields events errors dynamicSource internalRetNames
      isInternal inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun stmts internalFunctions =
    compileStmtList fields events errors dynamicSource internalRetNames isInternal
      inScopeNames adtTypes stmts internalFunctions := rfl

/-- Per-statement union of the proved EVMYulLean safe-body fragments.

A statement admitted here compiles (via `compileStmt`) into a Yul statement
list accepted by `BridgedStmts` with no nested function definitions. Internal
helper calls and typed external call binds are admitted through an explicit
`BridgedFunctionTable` witness. The `Bool` index is `isInternal`: arms that
only hold for external (resp. internal) bodies pin it to `false`
(resp. `true`); all other arms are polymorphic in it. -/
inductive BridgedSourceStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    Bool → Stmt → Prop
  | externalRecursiveRawLog {stmt : Stmt}
      (h : BridgedSourceExternalRecursiveBodyWithRawLogStmt
        fields errors dynamicSource stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames false stmt
  | internalRecursiveRawLog {stmt : Stmt}
      (h : BridgedSourceInternalRecursiveBodyWithRawLogStmt
        fields errors dynamicSource stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames true stmt
  | storage {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStorageStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | storageAddr {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStorageAddrStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | require {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceRequireStmt fields dynamicSource stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | setStorageArrayElement {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceSetStorageArrayElementStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingChain {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingChainStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingWrite {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingWriteStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingWriteMultiSlot {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingWriteMultiSlotStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingWrite2 {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingWrite2Stmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingWrite2MultiSlot {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingWrite2MultiSlotStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | structMember {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStructMemberStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | structMember2 {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStructMember2Stmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | structMemberNonzero {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStructMemberNonzeroStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | structMember2Nonzero {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStructMember2NonzeroStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | structMemberMultiSlot {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStructMemberMultiSlotStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | structMember2MultiSlot {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStructMember2MultiSlotStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingWord {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingWordStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mapping2Word {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMapping2WordStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingWordNonzero {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingWordNonzeroStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mapping2WordNonzero {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMapping2WordNonzeroStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingWordMultiSlot {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingWordMultiSlotStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mapping2WordMultiSlot {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMapping2WordMultiSlotStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingWordMultiSlotNonzero {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingWordMultiSlotNonzeroStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mapping2WordMultiSlotNonzero {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMapping2WordMultiSlotNonzeroStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | structMemberMultiSlotNonzero {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStructMemberMultiSlotNonzeroStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | structMember2MultiSlotNonzero {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStructMember2MultiSlotNonzeroStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingPackedWord {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingPackedWordStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingPackedWordNonzero {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingPackedWordNonzeroStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingPackedWordMultiSlot {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingPackedWordMultiSlotStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | mappingPackedWordMultiSlotNonzero {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMappingPackedWordMultiSlotNonzeroStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | returnValuesExternal {stmt : Stmt}
      (h : BridgedSourceReturnValuesExternalStmt stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames false stmt
  | returnValuesInternal {stmt : Stmt}
      (h : BridgedSourceReturnValuesInternalStmt internalRetNames stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames true stmt
  | mstore {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceMstoreStmt stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | tstore {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceTstoreStmt stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | calldatacopy {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceCalldatacopyStmt stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | returndatacopy {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceReturndatacopyStmt stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | revertReturndata {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceRevertReturndataStmt stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | storageArrayPush {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStorageArrayPushStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | storageArrayPop {isInternal : Bool} {stmt : Stmt}
      (h : BridgedSourceStorageArrayPopStmt fields stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | internalCall {isInternal : Bool} {stmt : Stmt}
      {table : BridgedFunctionTable}
      (h : BridgedSourceInternalCallStmt table stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt
  | externalCallBind {isInternal : Bool} {stmt : Stmt}
      {table : BridgedFunctionTable}
      (h : BridgedSourceExternalCallBindStmt table stmt) :
      BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt

/-- Master per-statement closure: every `BridgedSourceStmt` compiles to a
Yul statement list accepted by `BridgedStmts`. One constructor dispatch with
each arm delegating to the matching fragment-specific closure lemma. -/
theorem compileStmt_bridgedSource_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceStmt fields errors dynamicSource internalRetNames
        isInternal stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | externalRecursiveRawLog h =>
      exact compileStmt_external_recursive_body_with_raw_log_bridged fields
        events errors dynamicSource internalRetNames inScopeNames h hOk
  | internalRecursiveRawLog h =>
      exact compileStmt_internal_recursive_body_with_raw_log_bridged fields
        events errors dynamicSource internalRetNames inScopeNames h hOk
  | storage h =>
      exact compileStmt_storage_fragment_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | storageAddr h =>
      exact compileStmt_storageAddr_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | require h =>
      cases h with
      | require cond message hFailCond =>
          exact compileStmt_require_bridged fields events errors
            dynamicSource internalRetNames _ inScopeNames hFailCond hOk
  | setStorageArrayElement h =>
      exact compileStmt_setStorageArrayElement_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingChain h =>
      exact compileStmt_mappingChain_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWrite h =>
      exact compileStmt_mappingWrite_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWriteMultiSlot h =>
      exact compileStmt_mappingWriteMultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWrite2 h =>
      exact compileStmt_mappingWrite2_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWrite2MultiSlot h =>
      exact compileStmt_mappingWrite2MultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMember h =>
      exact compileStmt_structMember_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMember2 h =>
      exact compileStmt_structMember2_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMemberNonzero h =>
      exact compileStmt_structMemberNonzero_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMember2Nonzero h =>
      exact compileStmt_structMember2Nonzero_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMemberMultiSlot h =>
      exact compileStmt_structMemberMultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMember2MultiSlot h =>
      exact compileStmt_structMember2MultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWord h =>
      exact compileStmt_mappingWord_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mapping2Word h =>
      exact compileStmt_mapping2Word_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWordNonzero h =>
      exact compileStmt_mappingWordNonzero_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mapping2WordNonzero h =>
      exact compileStmt_mapping2WordNonzero_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWordMultiSlot h =>
      exact compileStmt_mappingWordMultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mapping2WordMultiSlot h =>
      exact compileStmt_mapping2WordMultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWordMultiSlotNonzero h =>
      exact compileStmt_mappingWordMultiSlotNonzero_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mapping2WordMultiSlotNonzero h =>
      exact compileStmt_mapping2WordMultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames _ inScopeNames h hOk
  | structMemberMultiSlotNonzero h =>
      exact compileStmt_structMemberMultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames _ inScopeNames h hOk
  | structMember2MultiSlotNonzero h =>
      exact compileStmt_structMember2MultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingPackedWord h =>
      exact compileStmt_mappingPackedWord_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingPackedWordNonzero h =>
      exact compileStmt_mappingPackedWordNonzero_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingPackedWordMultiSlot h =>
      exact compileStmt_mappingPackedWordMultiSlot_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingPackedWordMultiSlotNonzero h =>
      exact compileStmt_mappingPackedWordMultiSlotNonzero_bridged fields
        events errors dynamicSource internalRetNames _ inScopeNames h hOk
  | returnValuesExternal h =>
      exact compileStmt_returnValuesExternal_fragment_bridged fields events
        errors dynamicSource internalRetNames inScopeNames h hOk
  | returnValuesInternal h =>
      exact compileStmt_returnValuesInternal_fragment_bridged fields events
        errors dynamicSource internalRetNames inScopeNames h hOk
  | mstore h =>
      exact compileStmt_mstore_fragment_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | tstore h =>
      exact compileStmt_tstore_fragment_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | calldatacopy h =>
      exact compileStmt_calldatacopy_fragment_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | returndatacopy h =>
      exact compileStmt_returndatacopy_fragment_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | revertReturndata h =>
      exact compileStmt_revertReturndata_fragment_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | storageArrayPush h =>
      exact compileStmt_storageArrayPush_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | storageArrayPop h =>
      exact compileStmt_storageArrayPop_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | internalCall h =>
      exact compileStmt_internalCall_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames [] h hOk
  | externalCallBind h =>
      exact compileStmt_externalCallBind_bridged fields events errors
        dynamicSource internalRetNames _ inScopeNames [] h hOk

/-- Master per-statement no-function-definition closure, mirroring
`compileStmt_bridgedSource_bridged`. -/
theorem compileStmt_bridgedSource_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceStmt fields errors dynamicSource internalRetNames
        isInternal stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | externalRecursiveRawLog h =>
      exact compileStmt_external_recursive_body_with_raw_log_noFuncDefs fields
        events errors dynamicSource internalRetNames inScopeNames h hOk
  | internalRecursiveRawLog h =>
      exact compileStmt_internal_recursive_body_with_raw_log_noFuncDefs fields
        events errors dynamicSource internalRetNames inScopeNames h hOk
  | storage h =>
      exact compileStmt_storage_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | storageAddr h =>
      exact compileStmt_storageAddr_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | require h =>
      cases h with
      | require cond message hFailCond =>
          exact compileStmt_require_noFuncDefs fields events errors
            dynamicSource internalRetNames _ inScopeNames hFailCond hOk
  | setStorageArrayElement h =>
      exact compileStmt_setStorageArrayElement_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingChain h =>
      exact compileStmt_mappingChain_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWrite h =>
      exact compileStmt_mappingWrite_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWriteMultiSlot h =>
      exact compileStmt_mappingWriteMultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWrite2 h =>
      exact compileStmt_mappingWrite2_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWrite2MultiSlot h =>
      exact compileStmt_mappingWrite2MultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMember h =>
      exact compileStmt_structMember_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMember2 h =>
      exact compileStmt_structMember2_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMemberNonzero h =>
      exact compileStmt_structMemberNonzero_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMember2Nonzero h =>
      exact compileStmt_structMember2Nonzero_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMemberMultiSlot h =>
      exact compileStmt_structMemberMultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | structMember2MultiSlot h =>
      exact compileStmt_structMember2MultiSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWord h =>
      exact compileStmt_mappingWord_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mapping2Word h =>
      exact compileStmt_mapping2Word_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWordNonzero h =>
      exact compileStmt_mappingWordNonzero_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mapping2WordNonzero h =>
      exact compileStmt_mapping2WordNonzero_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWordMultiSlot h =>
      exact compileStmt_mappingWordMultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mapping2WordMultiSlot h =>
      exact compileStmt_mapping2WordMultiSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingWordMultiSlotNonzero h =>
      exact compileStmt_mappingWordMultiSlotNonzero_noFuncDefs fields events
        errors dynamicSource internalRetNames _ inScopeNames h hOk
  | mapping2WordMultiSlotNonzero h =>
      exact compileStmt_mapping2WordMultiSlotNonzero_noFuncDefs fields
        events errors dynamicSource internalRetNames _ inScopeNames h hOk
  | structMemberMultiSlotNonzero h =>
      exact compileStmt_structMemberMultiSlotNonzero_noFuncDefs fields
        events errors dynamicSource internalRetNames _ inScopeNames h hOk
  | structMember2MultiSlotNonzero h =>
      exact compileStmt_structMember2MultiSlotNonzero_noFuncDefs fields
        events errors dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingPackedWord h =>
      exact compileStmt_mappingPackedWord_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingPackedWordNonzero h =>
      exact compileStmt_mappingPackedWordNonzero_noFuncDefs fields events
        errors dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingPackedWordMultiSlot h =>
      exact compileStmt_mappingPackedWordMultiSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames _ inScopeNames h hOk
  | mappingPackedWordMultiSlotNonzero h =>
      exact compileStmt_mappingPackedWordMultiSlotNonzero_noFuncDefs fields
        events errors dynamicSource internalRetNames _ inScopeNames h hOk
  | returnValuesExternal h =>
      exact compileStmt_returnValuesExternal_fragment_noFuncDefs fields events
        errors dynamicSource internalRetNames inScopeNames h hOk
  | returnValuesInternal h =>
      exact compileStmt_returnValuesInternal_fragment_noFuncDefs fields events
        errors dynamicSource internalRetNames inScopeNames h hOk
  | mstore h =>
      exact compileStmt_mstore_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | tstore h =>
      exact compileStmt_tstore_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | calldatacopy h =>
      exact compileStmt_calldatacopy_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | returndatacopy h =>
      exact compileStmt_returndatacopy_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | revertReturndata h =>
      exact compileStmt_revertReturndata_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | storageArrayPush h =>
      exact compileStmt_storageArrayPush_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | storageArrayPop h =>
      exact compileStmt_storageArrayPop_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames h hOk
  | internalCall h =>
      exact compileStmt_internalCall_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames [] h hOk
  | externalCallBind h =>
      exact compileStmt_externalCallBind_noFuncDefs fields events errors
        dynamicSource internalRetNames _ inScopeNames [] h hOk

/-- Cons-inversion of `compileStmtList`, local copy of the (private) generic
inversion used by the call-closure module. -/
private theorem compileStmtList_cons_ok_inv
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {internalRetNames : List String}
    {isInternal : Bool} {adtTypes : List AdtTypeDef}
    {stmt : Stmt} {rest : List Stmt} {inScopeNames : List String}
    {bodyIR : List YulStmt}
    (hOk : compileStmtList fields events errors dynamicSource internalRetNames
      isInternal inScopeNames adtTypes (stmt :: rest) = .ok bodyIR) :
    ∃ headIR tailIR,
      compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames adtTypes stmt = .ok headIR ∧
      compileStmtList fields events errors dynamicSource internalRetNames
          isInternal (collectStmtBindNames stmt ++ inScopeNames) adtTypes rest =
        .ok tailIR ∧
      bodyIR = headIR ++ tailIR := by
  simp only [compileStmtList] at hOk
  unfold compileStmtListWithFork at hOk
  simp only [bind, Except.bind] at hOk
  rw [compileStmtWithFork_cancun_eq_compileStmt] at hOk
  cases hHead : compileStmt fields events errors dynamicSource internalRetNames
    isInternal inScopeNames adtTypes stmt with
  | error _ => simp [hHead] at hOk
  | ok headIR =>
    simp [hHead] at hOk
    cases hTail : compileStmtList fields events errors dynamicSource
      internalRetNames isInternal (collectStmtBindNames stmt ++ inScopeNames)
      adtTypes rest with
    | error _ => simp [compileStmtListWithFork_cancun_eq_compileStmtList, hTail] at hOk
    | ok tailIR =>
      simp [compileStmtListWithFork_cancun_eq_compileStmtList, hTail, Pure.pure, Except.pure] at hOk
      exact ⟨headIR, tailIR, rfl, rfl, hOk.symm⟩

/-- List-level lift of the master per-statement closure: a statement list
whose members are all `BridgedSourceStmt` compiles to a `BridgedStmts`
output. -/
theorem compileStmtList_bridgedSource_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt),
      (∀ stmt ∈ stmts,
        BridgedSourceStmt fields errors dynamicSource internalRetNames
          isInternal stmt) →
      ∀ (inScopeNames : List String) {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
      intro _ _ out hOk
      simp only [compileStmtList] at hOk
      unfold compileStmtListWithFork at hOk
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hOk
      subst out
      intro _ hMem
      cases hMem
  | cons s ss ih =>
      intro hAll inScopeNames out hOk
      obtain ⟨headOut, tailOut, hHead, hTail, hEq⟩ :=
        compileStmtList_cons_ok_inv hOk
      subst hEq
      exact BridgedStmts_append
        (compileStmt_bridgedSource_bridged fields events errors dynamicSource
          internalRetNames isInternal inScopeNames
          (hAll s List.mem_cons_self) hHead)
        (ih (fun s' hMem => hAll s' (List.mem_cons_of_mem s hMem)) _ hTail)

/-- List-level lift of the master per-statement no-function-definition
closure. -/
theorem compileStmtList_bridgedSource_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt),
      (∀ stmt ∈ stmts,
        BridgedSourceStmt fields errors dynamicSource internalRetNames
          isInternal stmt) →
      ∀ (inScopeNames : List String) {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmts
  induction stmts with
  | nil =>
      intro _ _ out hOk
      simp only [compileStmtList] at hOk
      unfold compileStmtListWithFork at hOk
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hOk
      subst out
      rfl
  | cons s ss ih =>
      intro hAll inScopeNames out hOk
      obtain ⟨headOut, tailOut, hHead, hTail, hEq⟩ :=
        compileStmtList_cons_ok_inv hOk
      subst hEq
      rw [Native.yulStmtsContainFuncDef_append]
      simp [compileStmt_bridgedSource_noFuncDefs fields events errors
          dynamicSource internalRetNames isInternal inScopeNames
          (hAll s List.mem_cons_self) hHead,
        ih (fun s' hMem => hAll s' (List.mem_cons_of_mem s hMem)) _ hTail]

end Compiler.Proofs.YulGeneration.Backends
