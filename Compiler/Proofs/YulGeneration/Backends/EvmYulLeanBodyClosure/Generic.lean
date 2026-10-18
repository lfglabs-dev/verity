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

section BridgedSourceFamilies

variable {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
  {dynamicSource : DynamicDataSource} {internalRetNames : List String}
  {isInternal : Bool} {inScopeNames : List String} {stmt : Stmt} {out : List YulStmt}
  {table : BridgedFunctionTable}

/-- Bridged and no-function-definition closure for the external-only
(`isInternal = false`) arms: recursive raw-log bodies and `returnValues`. -/
private theorem compileStmt_externalOnlyFamily_closure
    (h : BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors dynamicSource stmt ∨
      BridgedSourceReturnValuesExternalStmt stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames false
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h
  · exact ⟨compileStmt_external_recursive_body_with_raw_log_bridged _ _ _ _ _ _ h hOk,
      compileStmt_external_recursive_body_with_raw_log_noFuncDefs _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_returnValuesExternal_fragment_bridged _ _ _ _ _ _ h hOk,
      compileStmt_returnValuesExternal_fragment_noFuncDefs _ _ _ _ _ _ h hOk⟩

/-- Bridged and no-function-definition closure for the internal-only
(`isInternal = true`) arms: recursive raw-log bodies and `returnValues`. -/
private theorem compileStmt_internalOnlyFamily_closure
    (h : BridgedSourceInternalRecursiveBodyWithRawLogStmt fields errors dynamicSource stmt ∨
      BridgedSourceReturnValuesInternalStmt internalRetNames stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames true
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h
  · exact ⟨compileStmt_internal_recursive_body_with_raw_log_bridged _ _ _ _ _ _ h hOk,
      compileStmt_internal_recursive_body_with_raw_log_noFuncDefs _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_returnValuesInternal_fragment_bridged _ _ _ _ _ _ h hOk,
      compileStmt_returnValuesInternal_fragment_noFuncDefs _ _ _ _ _ _ h hOk⟩

/-- Bridged and no-function-definition closure for the call arms:
internal helper calls and typed external call binds via a function table. -/
private theorem compileStmt_callFamily_closure
    (h : BridgedSourceInternalCallStmt table stmt ∨
      BridgedSourceExternalCallBindStmt table stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h
  · exact ⟨compileStmt_internalCall_bridged _ _ _ _ _ _ _ [] h hOk,
      compileStmt_internalCall_noFuncDefs _ _ _ _ _ _ _ [] h hOk⟩
  · exact ⟨compileStmt_externalCallBind_bridged _ _ _ _ _ _ _ [] h hOk,
      compileStmt_externalCallBind_noFuncDefs _ _ _ _ _ _ _ [] h hOk⟩

/-- Bridged and no-function-definition closure for the plain-storage
arms: scalar/address slots, `require`, and storage arrays. -/
private theorem compileStmt_storageFamily_closure
    (h : BridgedSourceStorageStmt fields stmt ∨ BridgedSourceStorageAddrStmt fields stmt ∨
      BridgedSourceRequireStmt fields dynamicSource stmt ∨
      BridgedSourceSetStorageArrayElementStmt fields stmt ∨
      BridgedSourceStorageArrayPushStmt fields stmt ∨
      BridgedSourceStorageArrayPopStmt fields stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h | h | h | h | h
  · exact ⟨compileStmt_storage_fragment_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_storage_fragment_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_storageAddr_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_storageAddr_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · cases h with
    | require _ _ h =>
        exact ⟨compileStmt_require_bridged _ _ _ _ _ _ _ h hOk,
          compileStmt_require_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_setStorageArrayElement_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_setStorageArrayElement_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_storageArrayPush_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_storageArrayPush_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_storageArrayPop_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_storageArrayPop_noFuncDefs _ _ _ _ _ _ _ h hOk⟩

/-- Bridged and no-function-definition closure for the mapping-write
arms: mapping chains and (multi-slot) one/two-key writes. -/
private theorem compileStmt_mappingWriteFamily_closure
    (h : BridgedSourceMappingChainStmt fields stmt ∨
      BridgedSourceMappingWriteStmt fields stmt ∨
      BridgedSourceMappingWriteMultiSlotStmt fields stmt ∨
      BridgedSourceMappingWrite2Stmt fields stmt ∨
      BridgedSourceMappingWrite2MultiSlotStmt fields stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h | h | h | h
  · exact ⟨compileStmt_mappingChain_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingChain_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mappingWrite_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingWrite_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mappingWriteMultiSlot_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingWriteMultiSlot_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mappingWrite2_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingWrite2_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mappingWrite2MultiSlot_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingWrite2MultiSlot_noFuncDefs _ _ _ _ _ _ _ h hOk⟩

/-- Bridged and no-function-definition closure for the struct-member
arms: plain, two-key and nonzero single-slot member writes. -/
private theorem compileStmt_structMemberFamily_closure
    (h : BridgedSourceStructMemberStmt fields stmt ∨
      BridgedSourceStructMember2Stmt fields stmt ∨
      BridgedSourceStructMemberNonzeroStmt fields stmt ∨
      BridgedSourceStructMember2NonzeroStmt fields stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h | h | h
  · exact ⟨compileStmt_structMember_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_structMember_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_structMember2_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_structMember2_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_structMemberNonzero_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_structMemberNonzero_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_structMember2Nonzero_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_structMember2Nonzero_noFuncDefs _ _ _ _ _ _ _ h hOk⟩

/-- Bridged and no-function-definition closure for the multi-slot
struct-member arms: plain, two-key and nonzero member writes. -/
private theorem compileStmt_structMemberMultiSlotFamily_closure
    (h : BridgedSourceStructMemberMultiSlotStmt fields stmt ∨
      BridgedSourceStructMember2MultiSlotStmt fields stmt ∨
      BridgedSourceStructMemberMultiSlotNonzeroStmt fields stmt ∨
      BridgedSourceStructMember2MultiSlotNonzeroStmt fields stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h | h | h
  · exact ⟨compileStmt_structMemberMultiSlot_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_structMemberMultiSlot_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_structMember2MultiSlot_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_structMember2MultiSlot_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_structMemberMultiSlotNonzero_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_structMemberMultiSlotNonzero_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_structMember2MultiSlotNonzero_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_structMember2MultiSlotNonzero_noFuncDefs _ _ _ _ _ _ _ h hOk⟩

/-- Bridged and no-function-definition closure for the mapping-word
arms: one/two-key and nonzero single-slot word writes. -/
private theorem compileStmt_mappingWordFamily_closure
    (h : BridgedSourceMappingWordStmt fields stmt ∨ BridgedSourceMapping2WordStmt fields stmt ∨
      BridgedSourceMappingWordNonzeroStmt fields stmt ∨
      BridgedSourceMapping2WordNonzeroStmt fields stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h | h | h
  · exact ⟨compileStmt_mappingWord_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingWord_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mapping2Word_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mapping2Word_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mappingWordNonzero_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingWordNonzero_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mapping2WordNonzero_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mapping2WordNonzero_noFuncDefs _ _ _ _ _ _ _ h hOk⟩

/-- Bridged and no-function-definition closure for the multi-slot
mapping-word arms: one/two-key and nonzero word writes. -/
private theorem compileStmt_mappingWordMultiSlotFamily_closure
    (h : BridgedSourceMappingWordMultiSlotStmt fields stmt ∨
      BridgedSourceMapping2WordMultiSlotStmt fields stmt ∨
      BridgedSourceMappingWordMultiSlotNonzeroStmt fields stmt ∨
      BridgedSourceMapping2WordMultiSlotNonzeroStmt fields stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h | h | h
  · exact ⟨compileStmt_mappingWordMultiSlot_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingWordMultiSlot_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mapping2WordMultiSlot_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mapping2WordMultiSlot_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mappingWordMultiSlotNonzero_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingWordMultiSlotNonzero_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mapping2WordMultiSlotNonzero_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mapping2WordMultiSlotNonzero_noFuncDefs _ _ _ _ _ _ _ h hOk⟩

/-- Bridged and no-function-definition closure for the packed
mapping-word arms: plain, nonzero and multi-slot packed writes. -/
private theorem compileStmt_mappingPackedWordFamily_closure
    (h : BridgedSourceMappingPackedWordStmt fields stmt ∨
      BridgedSourceMappingPackedWordNonzeroStmt fields stmt ∨
      BridgedSourceMappingPackedWordMultiSlotStmt fields stmt ∨
      BridgedSourceMappingPackedWordMultiSlotNonzeroStmt fields stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h | h | h
  · exact ⟨compileStmt_mappingPackedWord_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingPackedWord_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mappingPackedWordNonzero_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingPackedWordNonzero_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mappingPackedWordMultiSlot_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingPackedWordMultiSlot_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_mappingPackedWordMultiSlotNonzero_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mappingPackedWordMultiSlotNonzero_noFuncDefs _ _ _ _ _ _ _ h hOk⟩

/-- Bridged and no-function-definition closure for the memory arms:
`mstore`, `tstore`, `calldatacopy`, `returndatacopy`, `revert(returndata)`. -/
private theorem compileStmt_memoryFamily_closure
    (h : BridgedSourceMstoreStmt stmt ∨ BridgedSourceTstoreStmt stmt ∨
      BridgedSourceCalldatacopyStmt stmt ∨ BridgedSourceReturndatacopyStmt stmt ∨
      BridgedSourceRevertReturndataStmt stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  rcases h with h | h | h | h | h
  · exact ⟨compileStmt_mstore_fragment_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_mstore_fragment_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_tstore_fragment_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_tstore_fragment_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_calldatacopy_fragment_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_calldatacopy_fragment_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_returndatacopy_fragment_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_returndatacopy_fragment_noFuncDefs _ _ _ _ _ _ _ h hOk⟩
  · exact ⟨compileStmt_revertReturndata_fragment_bridged _ _ _ _ _ _ _ h hOk,
      compileStmt_revertReturndata_fragment_noFuncDefs _ _ _ _ _ _ _ h hOk⟩

/-- Shared per-statement closure behind both master theorems: every
`BridgedSourceStmt` compiles to a `BridgedStmts` output that contains no
function definitions. Each constructor is routed to its family helper above,
whose disjunctive hypothesis is discharged from the constructor premise. -/
private theorem compileStmt_bridgedSource_closure
    (hStmt : BridgedSourceStmt fields errors dynamicSource internalRetNames isInternal stmt)
    (hOk : compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames [] stmt = .ok out) :
    BridgedStmts out ∧ Native.yulStmtsContainFuncDef out = false := by
  cases hStmt <;> rename_i h <;> first
    | exact compileStmt_externalOnlyFamily_closure (by simp [h]) hOk
    | exact compileStmt_internalOnlyFamily_closure (by simp [h]) hOk
    | exact compileStmt_callFamily_closure (by first | exact .inl h | exact .inr h) hOk
    | exact compileStmt_storageFamily_closure (by simp [h]) hOk
    | exact compileStmt_mappingWriteFamily_closure (by simp [h]) hOk
    | exact compileStmt_structMemberFamily_closure (by simp [h]) hOk
    | exact compileStmt_structMemberMultiSlotFamily_closure (by simp [h]) hOk
    | exact compileStmt_mappingWordFamily_closure (by simp [h]) hOk
    | exact compileStmt_mappingWordMultiSlotFamily_closure (by simp [h]) hOk
    | exact compileStmt_mappingPackedWordFamily_closure (by simp [h]) hOk
    | exact compileStmt_memoryFamily_closure (by simp [h]) hOk

end BridgedSourceFamilies

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
  exact (compileStmt_bridgedSource_closure hStmt hOk).1

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
  exact (compileStmt_bridgedSource_closure hStmt hOk).2

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
