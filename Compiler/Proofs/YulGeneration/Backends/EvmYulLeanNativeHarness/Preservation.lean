import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness.Foundation

import Lean

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul

open Compiler.Proofs.YulGeneration

open Compiler.Proofs.YulGeneration.Backends.StateBridge

open Lean Elab Tactic Meta

open Compiler.Proofs.IRGeneration

  (IRResult IRState IRStorageSlot IRStorageWord IRTransaction)

theorem state_getElem_overwrite?_left
    (state next : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (hOk : ∃ shared store, next = EvmYul.Yul.State.Ok shared store) :
    (state.overwrite? next)[name]! = state[name]! := by
  rcases hOk with ⟨shared, store, rfl⟩
  cases state <;> rfl

theorem state_getElem_restoreCallFrame_of_ok
    (state next : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (hState : ∃ shared store, state = EvmYul.Yul.State.Ok shared store)
    (hNext : ∃ shared store, next.reviveJump = EvmYul.Yul.State.Ok shared store) :
    ((next.reviveJump.overwrite? state).setStore state)[name]! = state[name]! := by
  rcases hState with ⟨shared, store, rfl⟩
  rcases hNext with ⟨shared', store', hNextOk⟩
  simp [EvmYul.Yul.State.overwrite?]
  rw [hNextOk, state_getElem_setStore_ok]

theorem native_call_preserves_lookup_of_revivable_body
    (name functionName : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (fuel : Nat)
    (values : List EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (rets : List EvmYul.Literal)
    (hLookup :
      ((EvmYul.Yul.State.Ok shared store) : EvmYul.Yul.State)[name]! =
        expected)
    (hRevivable :
      ∀ (yulContract : EvmYul.Account .Yul)
        (functionDef : EvmYul.Yul.Ast.FunctionDefinition)
        (calleeState : EvmYul.Yul.State),
        (codeOverride.getD yulContract.code).functions.lookup functionName =
          some functionDef →
        EvmYul.Yul.exec (fuel - 1)
          (.Block functionDef.body) codeOverride
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall functionDef.params values
              (EvmYul.Yul.State.Ok shared store))) =
          .ok calleeState →
        ∃ shared' store',
          calleeState.reviveJump = EvmYul.Yul.State.Ok shared' store')
    (hCall :
      EvmYul.Yul.call fuel values (some functionName) codeOverride
          (EvmYul.Yul.State.Ok shared store) =
        .ok (final, rets)) :
    final[name]! = expected := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.call] at hCall
  | succ fuel' =>
      simp only [EvmYul.Yul.call] at hCall
      cases hCode :
          (EvmYul.Yul.State.Ok shared store).sharedState.accountMap.get?
            (EvmYul.Yul.State.Ok shared store).executionEnv.codeOwner with
      | none =>
          change
            (match
                Std.TreeMap.get?
                    (EvmYul.Yul.State.Ok shared store).sharedState.accountMap
                    (EvmYul.Yul.State.Ok shared store).executionEnv.codeOwner with
              | none =>
                  (Except.error
                    (EvmYul.Yul.Exception.MissingContract
                      s!"{(EvmYul.Yul.State.Ok shared store).executionEnv.codeOwner}") :
                    Except EvmYul.Yul.Exception
                      (EvmYul.Yul.State × List EvmYul.Literal))
              | some _ => _ ) = .ok (final, rets) at hCall
          rw [hCode] at hCall
          cases hCall
      | some yulContract =>
          have hCode' :
              getElem? (EvmYul.Yul.State.Ok shared store).sharedState.accountMap
                (EvmYul.Yul.State.Ok shared store).executionEnv.codeOwner =
                  some yulContract := by
            rw [← Std.TreeMap.get?_eq_getElem?]
            exact hCode
          simp [hCode'] at hCall
          split at hCall
          next hFunction =>
            cases hCall
          next functionDef hFunction =>
            split at hCall
            next err hExec =>
              cases hCall
            next calleeState hExec =>
              rcases hCall with ⟨hFinal, _⟩
              exact
                state_getElem_restoreCallFrame_of_ok
                  (EvmYul.Yul.State.Ok shared store) calleeState name
                  ⟨shared, store, rfl⟩
                  (hRevivable yulContract functionDef calleeState
                    hFunction (by simpa using hExec)) ▸ hLookup

theorem nativeMappingSlotFunctionDefinition_exec_revivable_of_ok_state
    (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state calleeState : EvmYul.Yul.State)
    (hState : ∃ shared store, state = EvmYul.Yul.State.Ok shared store)
    (hExec :
      EvmYul.Yul.exec fuel (.Block nativeMappingSlotFunctionDefinition.body)
        codeOverride state = .ok calleeState) :
    ∃ shared' store',
      calleeState.reviveJump = EvmYul.Yul.State.Ok shared' store' := by
  rcases hState with ⟨shared, store, rfl⟩
  exact
    nativeMappingSlotFunctionDefinition_exec_revivable fuel codeOverride
      shared store calleeState hExec

theorem state_foldr_insert_ok_exists
    (entries : List (EvmYul.Identifier × EvmYul.Literal))
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    ∃ shared' store',
      entries.foldr (fun entry state =>
          EvmYul.Yul.State.insert entry.1 entry.2 state)
        (EvmYul.Yul.State.Ok shared store) =
        EvmYul.Yul.State.Ok shared' store' := by
  induction entries with
  | nil =>
      exact ⟨shared, store, rfl⟩
  | cons entry entries ih =>
      rcases ih with ⟨shared', store', h⟩
      rw [List.foldr_cons, h]
      exact ⟨shared', store'.insert entry.1 entry.2, rfl⟩

theorem state_mkOk_initcall_ok_exists
    (params : List EvmYul.Identifier)
    (values : List EvmYul.Literal)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    ∃ shared' store',
      EvmYul.Yul.State.mkOk
        (EvmYul.Yul.State.initcall params values
          (EvmYul.Yul.State.Ok shared store)) =
        EvmYul.Yul.State.Ok shared' store' := by
  simp only [EvmYul.Yul.State.initcall, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.multifill, EvmYul.Yul.State.mkOk]
  let emptyStore : EvmYul.Yul.VarStore := Inhabited.default
  have hDefault : (Inhabited.default : EvmYul.Yul.State) =
      EvmYul.Yul.State.Ok (Inhabited.default : EvmYul.SharedState .Yul)
        emptyStore := rfl
  rw [hDefault]
  simp only
  rcases state_foldr_insert_ok_exists (List.zip params values) shared
      emptyStore with
    ⟨shared', store', hFill⟩
  exact ⟨shared', store', by rw [hFill]⟩

theorem native_mappingSlot_call_preserves_lookup
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (fuel : Nat)
    (values : List EvmYul.Literal)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (rets : List EvmYul.Literal)
    (hLookup :
      ((EvmYul.Yul.State.Ok shared store) : EvmYul.Yul.State)[name]! =
        expected)
    (hCall :
      EvmYul.Yul.call fuel values (some "mappingSlot")
          (some
            { dispatcher := dispatcher
              functions := ((∅ : NativeFunctionMap).insert
                "mappingSlot" nativeMappingSlotFunctionDefinition) })
          (EvmYul.Yul.State.Ok shared store) =
        .ok (final, rets)) :
    final[name]! = expected := by
  apply
    native_call_preserves_lookup_of_revivable_body name "mappingSlot"
      expected fuel values
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) })
      shared store final rets hLookup
  · intro yulContract functionDef calleeState hFunction hExec
    simp only [Option.getD_some] at hFunction
    change
      (((∅ : NativeFunctionMap).insert
        ("mappingSlot" : EvmYul.Yul.Ast.YulFunctionName)
        nativeMappingSlotFunctionDefinition).lookup
        ("mappingSlot" : EvmYul.Yul.Ast.YulFunctionName) =
        some functionDef) at hFunction
    rw [Finmap.lookup_insert] at hFunction
    injection hFunction with hDef
    subst functionDef
    exact
      nativeMappingSlotFunctionDefinition_exec_revivable_of_ok_state
        (fuel - 1)
        (some
          { dispatcher := dispatcher
            functions := ((∅ : NativeFunctionMap).insert
              "mappingSlot" nativeMappingSlotFunctionDefinition) })
        (EvmYul.Yul.State.mkOk
          (EvmYul.Yul.State.initcall nativeMappingSlotFunctionDefinition.params
            values (EvmYul.Yul.State.Ok shared store)))
        calleeState
        (state_mkOk_initcall_ok_exists
          nativeMappingSlotFunctionDefinition.params values shared store)
        hExec
  · exact hCall

theorem native_mappingSlot_call_preserves_lookup_state
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (fuel : Nat)
    (values : List EvmYul.Literal)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (state final : EvmYul.Yul.State)
    (rets : List EvmYul.Literal)
    (hLookup : state[name]! = expected)
    (hCall :
      EvmYul.Yul.call fuel values (some "mappingSlot")
          (some
            { dispatcher := dispatcher
              functions := ((∅ : NativeFunctionMap).insert
                "mappingSlot" nativeMappingSlotFunctionDefinition) })
          state =
        .ok (final, rets)) :
    final[name]! = expected := by
  cases state with
  | Ok shared store =>
      exact
        native_mappingSlot_call_preserves_lookup name expected fuel values
          dispatcher shared store final rets hLookup hCall
  | OutOfFuel =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.call] at hCall
      | succ fuel' =>
          simp only [EvmYul.Yul.call] at hCall
          cases hCode :
              EvmYul.Yul.State.OutOfFuel.sharedState.accountMap.get?
                EvmYul.Yul.State.OutOfFuel.executionEnv.codeOwner with
          | none =>
              rw [hCode] at hCall
              cases hCall
          | some yulContract =>
              rw [hCode] at hCall
              simp only [Option.getD_some] at hCall
              split at hCall
              next hFunction =>
                cases hCall
              next functionDef hFunction =>
                split at hCall
                next err hExec =>
                  cases hCall
                next calleeState hExec =>
                  simp only [EvmYul.Yul.State.overwrite?,
                    EvmYul.Yul.State.setStore] at hCall
                  rcases hCall with ⟨rfl, _⟩
                  exact hLookup
  | Checkpoint jump =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.call] at hCall
      | succ fuel' =>
          simp only [EvmYul.Yul.call] at hCall
          cases hCode :
              (EvmYul.Yul.State.Checkpoint jump).sharedState.accountMap.get?
                (EvmYul.Yul.State.Checkpoint jump).executionEnv.codeOwner with
          | none =>
              simp [hCode] at hCall
          | some yulContract =>
              simp [hCode] at hCall
              cases hExec :
                  EvmYul.Yul.exec fuel'
                    (.Block nativeMappingSlotFunctionDefinition.body)
                    (some
                      { dispatcher := dispatcher
                        functions := ((∅ : NativeFunctionMap).insert
                          "mappingSlot" nativeMappingSlotFunctionDefinition) })
                    (EvmYul.Yul.State.mkOk
                      (EvmYul.Yul.State.initcall
                        nativeMappingSlotFunctionDefinition.params values
                        (EvmYul.Yul.State.Checkpoint jump))) with
              | error err =>
                  simp [hExec] at hCall
              | ok calleeState =>
                  simp [hExec, EvmYul.Yul.State.overwrite?,
                    EvmYul.Yul.State.setStore] at hCall
                  rcases hCall with ⟨rfl, _⟩
                  exact hLookup

theorem NativeExprPreservesWord_lowerExprNative_mappingSlot_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse)
        (some
          { dispatcher := dispatcher
            functions := ((∅ : NativeFunctionMap).insert
              "mappingSlot" nativeMappingSlotFunctionDefinition) })) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.call "mappingSlot" args))
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
  NativeExprPreservesWord_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves
    name "mappingSlot" expected args
    (some
      { dispatcher := dispatcher
        functions := ((∅ : NativeFunctionMap).insert
          "mappingSlot" nativeMappingSlotFunctionDefinition) })
    (by rfl) hArgs
    (by
      intro fuel state values final rets hLookup hCall
      exact
        native_mappingSlot_call_preserves_lookup_state name expected fuel
          values dispatcher state final rets hLookup hCall)

theorem NativeExprPreservesWord_lowerExprNative_of_bridgedExpr_mappingContract
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (expr : YulExpr)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hExpr : Compiler.Proofs.YulGeneration.Backends.BridgedExpr expr) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative expr)
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  induction hExpr with
  | lit n =>
      exact NativeExprPreservesWord_lowerExprNative_lit name expected n _
  | hex n =>
      exact NativeExprPreservesWord_lowerExprNative_hex name expected n _
  | str s =>
      exact NativeExprPreservesWord_lowerExprNative_str name expected s _
  | ident ident =>
      exact NativeExprPreservesWord_lowerExprNative_ident name expected ident _
  | call func args hName hArgs ih =>
      have hNativeArgs :
          NativeEvalArgsPreservesWord name expected
            ((args.map Backends.lowerExprNative).reverse)
            (some
              { dispatcher := dispatcher
                functions := ((∅ : NativeFunctionMap).insert
                  "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
        NativeEvalArgsPreservesWord_map_lowerExprNative_reverse
          name expected args _ (by
            intro arg hArg
            exact ih arg hArg)
      by_cases hMapping : func = "mappingSlot"
      · subst func
        exact
          NativeExprPreservesWord_lowerExprNative_mappingSlot_of_nativeEvalArgs
            name expected args dispatcher hNativeArgs
      · cases hOp : Backends.lookupRuntimePrimOp func with
        | some op =>
            exact
              NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
                name func expected args op _ hOp hNativeArgs
                (NativePrimCallPreservesWord_of_allowed_lookupRuntimePrimOp
                  name func expected op hName hOp)
        | none =>
            exfalso
            exact lookupRuntimePrimOp_ne_none_of_allowed_of_ne_mappingSlot
              func hName hMapping hOp

theorem NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg) :
    NativeEvalArgsPreservesWord name expected
      ((args.map Backends.lowerExprNative).reverse)
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
  NativeEvalArgsPreservesWord_map_lowerExprNative_reverse
    name expected args
    (some
      { dispatcher := dispatcher
        functions := ((∅ : NativeFunctionMap).insert
          "mappingSlot" nativeMappingSlotFunctionDefinition) })
    (by
      intro arg hArg
      exact
        NativeExprPreservesWord_lowerExprNative_of_bridgedExpr_mappingContract
          name expected arg dispatcher (hArgs arg hArg))

/-- Mapping-free expression fragment for native matched-word preservation.

This mirrors `BridgedExpr` but excludes `mappingSlot` calls recursively, so the
native proof can target the actual lowered runtime contract instead of the
synthetic mapping-helper contract. -/
inductive NativeMappingFreeBridgedExpr : YulExpr → Prop
  | lit (n : Nat) : NativeMappingFreeBridgedExpr (.lit n)
  | hex (n : Nat) : NativeMappingFreeBridgedExpr (.hex n)
  | str (s : String) : NativeMappingFreeBridgedExpr (.str s)
  | ident (name : String) : NativeMappingFreeBridgedExpr (.ident name)
  | call (func : String) (args : List YulExpr)
      (hName : Compiler.Proofs.YulGeneration.Backends.allowedExprCallName func)
      (hNoMapping : func ≠ "mappingSlot")
      (hArgs : ∀ arg, arg ∈ args → NativeMappingFreeBridgedExpr arg) :
      NativeMappingFreeBridgedExpr (.call func args)

/-- Mapping-free bridged expressions preserve a marker word for any native
runtime contract override.

The only user-function-shaped call admitted by the historical bridged
expression predicate is `mappingSlot`; excluding it leaves only runtime
primitive calls, whose preservation proof is contract-independent. -/
theorem NativeExprPreservesWord_lowerExprNative_of_mappingFreeBridgedExpr
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (expr : YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hExpr : NativeMappingFreeBridgedExpr expr) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative expr) codeOverride := by
  induction hExpr with
  | lit n =>
      exact NativeExprPreservesWord_lowerExprNative_lit name expected n _
  | hex n =>
      exact NativeExprPreservesWord_lowerExprNative_hex name expected n _
  | str s =>
      exact NativeExprPreservesWord_lowerExprNative_str name expected s _
  | ident ident =>
      exact NativeExprPreservesWord_lowerExprNative_ident name expected ident _
  | call func args hName hNoMapping hArgs ih =>
      have hNativeArgs :
          NativeEvalArgsPreservesWord name expected
            ((args.map Backends.lowerExprNative).reverse) codeOverride :=
        NativeEvalArgsPreservesWord_map_lowerExprNative_reverse
          name expected args codeOverride (by
            intro arg hArg
            exact ih arg hArg)
      cases hOp : Backends.lookupRuntimePrimOp func with
      | some op =>
          exact
            NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
              name func expected args op codeOverride hOp hNativeArgs
              (NativePrimCallPreservesWord_of_allowed_lookupRuntimePrimOp
                name func expected op hName hOp)
      | none =>
          exfalso
          exact lookupRuntimePrimOp_ne_none_of_allowed_of_ne_mappingSlot
            func hName hNoMapping hOp

theorem NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ arg, arg ∈ args → NativeMappingFreeBridgedExpr arg) :
    NativeEvalArgsPreservesWord name expected
      ((args.map Backends.lowerExprNative).reverse) codeOverride :=
  NativeEvalArgsPreservesWord_map_lowerExprNative_reverse
    name expected args codeOverride (by
      intro arg hArg
      exact
        NativeExprPreservesWord_lowerExprNative_of_mappingFreeBridgedExpr
          name expected arg codeOverride (hArgs arg hArg))

theorem nativeSwitchDiscrTempName_ne_matchedTempName
    (switchId : Nat) :
    Backends.nativeSwitchDiscrTempName switchId ≠
      Backends.nativeSwitchMatchedTempName switchId := by
  intro h
  have hlen := congrArg String.length h
  have hd :
      (toString "__verity_native_switch_discr_").length = 29 := by
    decide
  have hm :
      (toString "__verity_native_switch_matched_").length = 31 := by
    decide
  simp [Backends.nativeSwitchDiscrTempName,
    Backends.nativeSwitchMatchedTempName, hd, hm] at hlen

theorem nativeSwitchPrefixFinalState_matched
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier) :
    (nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName)[matchedName]! = EvmYul.UInt256.ofNat 0 := by
  simp [nativeSwitchPrefixFinalState, nativeSwitchInitialOkState,
    EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

theorem nativeSwitchPrefixFinalState_discr
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier)
    (selector : Nat)
    (hne : discrName ≠ matchedName)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus) :
    (nativeSwitchPrefixFinalState contract tx storage observableSlots discrName matchedName)[discrName]! =
      EvmYul.UInt256.ofNat selector := by
  rw [hSelector]
  simp [nativeSwitchPrefixFinalState, nativeSwitchInitialOkState,
    EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]
  rw [Finmap.lookup_insert_of_ne]
  · rw [Finmap.lookup_insert]
    simp
  · exact hne

theorem nativeSwitchPrefixFinalState_marked
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier) :
    ((nativeSwitchPrefixFinalState contract tx storage observableSlots discrName matchedName).insert matchedName (EvmYul.UInt256.ofNat 1))[matchedName]! =
      EvmYul.UInt256.ofNat 1 := by
  simp [nativeSwitchPrefixFinalState, nativeSwitchInitialOkState,
    EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

def nativeSwitchPrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat) :
    EvmYul.Yul.State :=
  nativeSwitchPrefixFinalState contract tx storage observableSlots
    (Backends.nativeSwitchDiscrTempName switchId)
    (Backends.nativeSwitchMatchedTempName switchId)

def nativeSwitchMarkedPrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat) :
    EvmYul.Yul.State :=
  (nativeSwitchPrefixStateForId contract tx storage observableSlots switchId).insert
    (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 1)

theorem NativeBlockPreservesWord_nil
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeBlockPreservesWord name value [] codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hExec
      exact hLookup

theorem NativeBlockPreservesWord_cons
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hHead :
      ∀ fuel state next,
        state[name]! = value →
          EvmYul.Yul.exec fuel stmt codeOverride state = .ok next →
            next[name]! = value)
    (hRest : NativeBlockPreservesWord name value rest codeOverride) :
    NativeBlockPreservesWord name value (stmt :: rest) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hStmt : EvmYul.Yul.exec fuel' stmt codeOverride state with
      | error err =>
          simp [hStmt] at hExec
      | ok next =>
          simp [hStmt] at hExec
          have hNext : next[name]! = value :=
            hHead fuel' state next hLookup hStmt
          exact hRest fuel' next final hNext hExec

theorem NativeBlockPreservesWord_cons_stmt
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hHead : NativeStmtPreservesWord name value stmt codeOverride)
    (hRest : NativeBlockPreservesWord name value rest codeOverride) :
    NativeBlockPreservesWord name value (stmt :: rest) codeOverride :=
  NativeBlockPreservesWord_cons name value stmt rest codeOverride hHead hRest

theorem NativeBlockPreservesWord_singleton
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hStmt : NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value [stmt] codeOverride := by
  exact NativeBlockPreservesWord_cons_stmt name value stmt [] codeOverride
    hStmt (NativeBlockPreservesWord_nil name value codeOverride)

/-! ## `_revived` block preservation: nil and Leave-singleton

These are the building blocks the Leave-ending body bridges (E2, E4) need.
For the nil case `.Block []`, the result equals the input, so the bridge is
purely an identity-cast through `reviveJump`. -/

theorem NativeBlockPreservesWord_revived_nil
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeBlockPreservesWord_revived name value [] codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero => simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      subst hExec
      exact hLookup

/-- Given a `_revived` head-stmt witness and a `_revived` rest-block witness,
build the cons block witness. Mirrors `NativeBlockPreservesWord_cons` for
the revived form. -/
theorem NativeBlockPreservesWord_revived_cons
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hHead : NativeStmtPreservesWord_revived name value stmt codeOverride)
    (hRest : NativeBlockPreservesWord_revived name value rest codeOverride) :
    NativeBlockPreservesWord_revived name value (stmt :: rest) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero => simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hStmt : EvmYul.Yul.exec fuel' stmt codeOverride state with
      | error err => simp [hStmt] at hExec
      | ok next =>
          simp [hStmt] at hExec
          have hNext := hHead fuel' state next hLookup hStmt
          exact hRest fuel' next final hNext hExec

theorem NativeBlockPreservesWord_revived_singleton
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hStmt : NativeStmtPreservesWord_revived name value stmt codeOverride) :
    NativeBlockPreservesWord_revived name value [stmt] codeOverride :=
  NativeBlockPreservesWord_revived_cons name value stmt [] codeOverride hStmt
    (NativeBlockPreservesWord_revived_nil name value codeOverride)

/-- Generated-switch matched flag endpoint for Leave-aware bodies. The body
    preservation proof is stated through `reviveJump`; once the final checkpoint
    has been revived to an `Ok` state, checkpoint state projections make the raw
    final lookup agree with the revived lookup expected by the switch tail. -/
theorem nativeSwitchMatchedFlag_of_revived_body_final
    (switchId : Nat)
    (matchedName : EvmYul.Identifier)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (initial final : EvmYul.Yul.State)
    (fuel : Nat)
    (shared : EvmYul.SharedState EvmYul.OperationType.Yul)
    (store : EvmYul.Yul.VarStore)
    (_hMatchedName : matchedName = Backends.nativeSwitchMatchedTempName switchId)
    (hPreserves :
      NativeBlockPreservesWord_revived matchedName
        (EvmYul.UInt256.ofNat 1) body codeOverride)
    (hInitial :
      initial.reviveJump[matchedName]! =
        EvmYul.UInt256.ofNat 1)
    (hExec :
      EvmYul.Yul.exec fuel (.Block body) codeOverride initial = .ok final)
    (hRevive : final.reviveJump = EvmYul.Yul.State.Ok shared store) :
    final[matchedName]! = EvmYul.UInt256.ofNat 1 := by
  have hRawRevived :
      final[matchedName]! =
        final.reviveJump[matchedName]! := by
    cases final <;> simp [EvmYul.Yul.State.reviveJump] at hRevive ⊢
    case Checkpoint jump =>
      cases jump <;>
        simp [EvmYul.Yul.State.revive, GetElem?.getElem!, decidableGetElem?,
          GetElem.getElem, EvmYul.Yul.State.lookup!, EvmYul.Yul.State.store]
          at hRevive ⊢
  exact hRawRevived.trans (hPreserves fuel initial final hInitial hExec)

/-- `_revived` `.Block` constructor wrapper — mirrors the OLD-form
`NativeStmtPreservesWord_block`. `.Block body` exec and a list-body
preservation share the same definition shape, so the witness is the
hypothesis directly. -/
theorem NativeStmtPreservesWord_revived_block
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hBody : NativeBlockPreservesWord_revived name value body codeOverride) :
    NativeStmtPreservesWord_revived name value (.Block body) codeOverride :=
  hBody

theorem NativeBlockPreservesWord_of_forall_stmt
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value body codeOverride := by
  induction body with
  | nil =>
      exact NativeBlockPreservesWord_nil name value codeOverride
  | cons stmt rest ih =>
      refine NativeBlockPreservesWord_cons_stmt name value stmt rest
        codeOverride ?_ ?_
      · exact hPreserves stmt (by simp)
      · exact ih (by
          intro stmt' hmem
          exact hPreserves stmt' (by simp [hmem]))

theorem NativeBlockPreservesWord_of_forall_stmt_write_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      ∀ stmt, stmt ∈ body → (name : String) ∉ Backends.nativeStmtWriteNames stmt)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        (name : String) ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value body codeOverride :=
  NativeBlockPreservesWord_of_forall_stmt name value body codeOverride
    (by
      intro stmt hmem
      exact hPreserves stmt hmem (hFresh stmt hmem))

theorem nativeStmtWriteNames_not_mem_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (body : List EvmYul.Yul.Ast.Stmt)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames body)
    (hMem : stmt ∈ body) :
    (name : String) ∉ Backends.nativeStmtWriteNames stmt := by
  induction body with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      simp only [Backends.nativeStmtsWriteNames] at hFresh
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · subst stmt
        intro hName
        exact hFresh (List.mem_append_left _ hName)
      · exact ih (fun hName => hFresh (List.mem_append_right _ hName)) hTail

theorem nativeStmtWriteNames_let_singleton_not_mem_ne
    (name target : EvmYul.Identifier)
    (value : Option EvmYul.Yul.Ast.Expr)
    (hFresh : (name : String) ∉ Backends.nativeStmtWriteNames (.Let [target] value)) :
    name ≠ target := by
  intro hEq
  subst target
  unfold EvmYul.Identifier at hFresh
  simp [Backends.nativeStmtWriteNames] at hFresh

theorem nativeStmtWriteNames_let_not_mem_vars
    (name : EvmYul.Identifier)
    (vars : List EvmYul.Identifier)
    (value : Option EvmYul.Yul.Ast.Expr)
    (hFresh : (name : String) ∉ Backends.nativeStmtWriteNames (.Let vars value)) :
    name ∉ vars := by
  intro hMem
  unfold EvmYul.Identifier at hFresh hMem
  apply hFresh
  simpa [Backends.nativeStmtWriteNames] using hMem

theorem nativeStmtWriteNames_lowerAssignNative_not_mem_ne
    (name target : EvmYul.Identifier)
    (value : YulExpr)
    (hFresh :
      (name : String) ∉ Backends.nativeStmtWriteNames
        (Backends.lowerAssignNative target value)) :
    name ≠ target := by
  exact nativeStmtWriteNames_let_singleton_not_mem_ne name target
    (some (Backends.lowerExprNative value))
    (by simpa [Backends.lowerAssignNative] using hFresh)

theorem collectYulStmtWriteNames_append
    (writeStmt : YulStmt → List String)
    (left right : List YulStmt) :
    Backends.collectYulStmtWriteNames writeStmt (left ++ right) =
      Backends.collectYulStmtWriteNames writeStmt left ++
        Backends.collectYulStmtWriteNames writeStmt right := by
  induction left with
  | nil =>
      simp [Backends.collectYulStmtWriteNames]
  | cons head tail ih =>
      simp [Backends.collectYulStmtWriteNames, ih, List.append_assoc]

theorem yulStmtsWriteNames_append
    (left right : List YulStmt) :
    Backends.yulStmtsWriteNames (left ++ right) =
      Backends.yulStmtsWriteNames left ++ Backends.yulStmtsWriteNames right := by
  induction left with
  | nil =>
      simp [Backends.yulStmtsWriteNames]
  | cons head tail ih =>
      simp [Backends.yulStmtsWriteNames, ih, List.append_assoc]

theorem yulStmtsWriteNames_cons
    (stmt : YulStmt)
    (rest : List YulStmt) :
    Backends.yulStmtsWriteNames (stmt :: rest) =
      Backends.yulStmtWriteNames stmt ++ Backends.yulStmtsWriteNames rest := by
  simp [Backends.yulStmtsWriteNames]

theorem yulStmtWriteNames_not_mem_of_yulStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (body : List YulStmt)
    (stmt : YulStmt)
    (hFresh : (name : String) ∉ Backends.yulStmtsWriteNames body)
    (hMem : stmt ∈ body) :
    (name : String) ∉ Backends.yulStmtWriteNames stmt := by
  induction body with
  | nil =>
      simp at hMem
  | cons head tail ih =>
  rw [yulStmtsWriteNames_cons] at hFresh
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · subst stmt
        intro hName
        apply hFresh
        exact List.mem_append_left _ hName
      · apply ih
        · intro hName
          apply hFresh
          exact List.mem_append_right _ hName
        · exact hTail

theorem collectNativeStmtWriteNames_append
    (writeStmt : EvmYul.Yul.Ast.Stmt → List String)
    (left right : List EvmYul.Yul.Ast.Stmt) :
    Backends.collectNativeStmtWriteNames writeStmt (left ++ right) =
      Backends.collectNativeStmtWriteNames writeStmt left ++
        Backends.collectNativeStmtWriteNames writeStmt right := by
  induction left with
  | nil =>
      simp [Backends.collectNativeStmtWriteNames]
  | cons head tail ih =>
      simp [Backends.collectNativeStmtWriteNames, ih, List.append_assoc]

theorem nativeStmtsWriteNames_append
    (left right : List EvmYul.Yul.Ast.Stmt) :
    Backends.nativeStmtsWriteNames (left ++ right) =
      Backends.nativeStmtsWriteNames left ++ Backends.nativeStmtsWriteNames right := by
  induction left with
  | nil =>
      simp [Backends.nativeStmtsWriteNames]
  | cons head tail ih =>
      simp [Backends.nativeStmtsWriteNames, ih, List.append_assoc]

theorem nativeStmtsWriteNames_cons
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt) :
    Backends.nativeStmtsWriteNames (stmt :: rest) =
      Backends.nativeStmtWriteNames stmt ++ Backends.nativeStmtsWriteNames rest := by
  simp [Backends.nativeStmtsWriteNames]

theorem nativeStmtsWriteNames_cons_not_mem_iff
    (name : EvmYul.Identifier)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt) :
    (name : String) ∉ Backends.nativeStmtsWriteNames (stmt :: rest) ↔
      (name : String) ∉ Backends.nativeStmtWriteNames stmt ∧
        (name : String) ∉ Backends.nativeStmtsWriteNames rest := by
  rw [nativeStmtsWriteNames_cons]
  constructor
  · intro hFresh
    exact ⟨fun hMem => hFresh (List.mem_append_left _ hMem),
      fun hMem => hFresh (List.mem_append_right _ hMem)⟩
  · intro hFresh hMem
    rcases hFresh with ⟨hHead, hTail⟩
    rcases List.mem_append.mp hMem with hMem | hMem
    · exact hHead hMem
    · exact hTail hMem

theorem nativeStmtsWriteNames_head_not_mem_of_cons_not_mem
    (name : EvmYul.Identifier)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames (stmt :: rest)) :
    (name : String) ∉ Backends.nativeStmtWriteNames stmt := by
  intro hMem
  apply hFresh
  rw [nativeStmtsWriteNames_cons]
  exact List.mem_append_left _ hMem

theorem nativeStmtsWriteNames_tail_not_mem_of_cons_not_mem
    (name : EvmYul.Identifier)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames (stmt :: rest)) :
    (name : String) ∉ Backends.nativeStmtsWriteNames rest := by
  intro hMem
  apply hFresh
  rw [nativeStmtsWriteNames_cons]
  exact List.mem_append_right _ hMem

theorem nativeStmtsWriteNames_left_not_mem_of_append_not_mem
    (name : EvmYul.Identifier)
    (left right : List EvmYul.Yul.Ast.Stmt)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames (left ++ right)) :
    (name : String) ∉ Backends.nativeStmtsWriteNames left := by
  intro hMem
  apply hFresh
  rw [nativeStmtsWriteNames_append]
  exact List.mem_append_left _ hMem

theorem nativeStmtsWriteNames_right_not_mem_of_append_not_mem
    (name : EvmYul.Identifier)
    (left right : List EvmYul.Yul.Ast.Stmt)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames (left ++ right)) :
    (name : String) ∉ Backends.nativeStmtsWriteNames right := by
  intro hMem
  apply hFresh
  rw [nativeStmtsWriteNames_append]
  exact List.mem_append_right _ hMem

theorem nativeStmtsWriteNames_append_not_mem_iff
    (name : EvmYul.Identifier)
    (left right : List EvmYul.Yul.Ast.Stmt) :
    (name : String) ∉ Backends.nativeStmtsWriteNames (left ++ right) ↔
      (name : String) ∉ Backends.nativeStmtsWriteNames left ∧
        (name : String) ∉ Backends.nativeStmtsWriteNames right := by
  rw [nativeStmtsWriteNames_append]
  constructor
  · intro hFresh
    exact ⟨fun hMem => hFresh (List.mem_append_left _ hMem),
      fun hMem => hFresh (List.mem_append_right _ hMem)⟩
  · intro hFresh hMem
    rcases hFresh with ⟨hLeft, hRight⟩
    rcases List.mem_append.mp hMem with hMem | hMem
    · exact hLeft hMem
    · exact hRight hMem

theorem NativeBlockPreservesWord_append_of_forall_stmt
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hLeft :
      ∀ stmt, stmt ∈ left →
        NativeStmtPreservesWord name value stmt codeOverride)
    (hRight :
      ∀ stmt, stmt ∈ right →
        NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value (left ++ right) codeOverride :=
  NativeBlockPreservesWord_of_forall_stmt name value (left ++ right)
    codeOverride
    (by
      intro stmt hMem
      rcases List.mem_append.mp hMem with hMem | hMem
      · exact hLeft stmt hMem
      · exact hRight stmt hMem)

theorem NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames body)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        (name : String) ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value body codeOverride :=
  NativeBlockPreservesWord_of_forall_stmt_write_not_mem name value body
    codeOverride
    (by
      intro stmt hMem
      exact nativeStmtWriteNames_not_mem_of_nativeStmtsWriteNames_not_mem
        name body stmt hFresh hMem)
    hPreserves

theorem NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames (stmt :: rest))
    (hHead :
      (name : String) ∉ Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord name value stmt codeOverride)
    (hRest :
      (name : String) ∉ Backends.nativeStmtsWriteNames rest →
        NativeBlockPreservesWord name value rest codeOverride) :
    NativeBlockPreservesWord name value (stmt :: rest) codeOverride :=
  NativeBlockPreservesWord_cons_stmt name value stmt rest codeOverride
    (hHead
      (nativeStmtsWriteNames_head_not_mem_of_cons_not_mem
        name stmt rest hFresh))
    (hRest
      (nativeStmtsWriteNames_tail_not_mem_of_cons_not_mem
        name stmt rest hFresh))

theorem NativeStmtPreservesWord_block
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hBody : NativeBlockPreservesWord name value body codeOverride) :
    NativeStmtPreservesWord name value (.Block body) codeOverride :=
  hBody

theorem NativeStmtPreservesWord_block_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames body)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        (name : String) ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeStmtPreservesWord name value (.Block body) codeOverride :=
  NativeStmtPreservesWord_block name value body codeOverride
    (NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
      name value body codeOverride hFresh hPreserves)

theorem NativeBlockPreservesWord_append_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hLeftFresh : (name : String) ∉ Backends.nativeStmtsWriteNames left)
    (hRightFresh : (name : String) ∉ Backends.nativeStmtsWriteNames right)
    (hLeft :
      ∀ stmt, stmt ∈ left →
        (name : String) ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride)
    (hRight :
      ∀ stmt, stmt ∈ right →
        (name : String) ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value (left ++ right) codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem name value
    (left ++ right) codeOverride
    (by
      rw [nativeStmtsWriteNames_append]
      intro hMem
      rw [List.mem_append] at hMem
      rcases hMem with hMem | hMem
      · exact hLeftFresh hMem
      · exact hRightFresh hMem)
    (by
      intro stmt hMem hFresh
      rw [List.mem_append] at hMem
      rcases hMem with hMem | hMem
      · exact hLeft stmt hMem hFresh
      · exact hRight stmt hMem hFresh)

theorem NativeBlockPreservesWord_append_of_nativeStmtsWriteNames_append_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames (left ++ right))
    (hLeft :
      ∀ stmt, stmt ∈ left →
        (name : String) ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride)
    (hRight :
      ∀ stmt, stmt ∈ right →
        (name : String) ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value (left ++ right) codeOverride :=
  NativeBlockPreservesWord_append_of_nativeStmtsWriteNames_not_mem
    name value left right codeOverride
    (nativeStmtsWriteNames_left_not_mem_of_append_not_mem
      name left right hFresh)
    (nativeStmtsWriteNames_right_not_mem_of_append_not_mem
      name left right hFresh)
    hLeft hRight

theorem NativeStmtPreservesWord_if_of_eval_self
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond :
      ∀ fuel state,
        state[name]! = value →
          ∃ condValue,
            EvmYul.Yul.eval fuel cond codeOverride state =
              .ok (state, condValue))
    (hBody : NativeBlockPreservesWord name value body codeOverride) :
    NativeStmtPreservesWord name value (.If cond body) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hCond fuel' state hLookup with ⟨condValue, hEval⟩
      simp [EvmYul.Yul.exec, hEval] at hExec
      by_cases hCondNonzero : condValue ≠ ⟨0⟩
      · simp [hCondNonzero] at hExec
        exact hBody fuel' state final hLookup hExec
      · have hCondZero : condValue = ⟨0⟩ := by
          exact Decidable.not_not.mp hCondNonzero
        simp [hCondZero] at hExec
        cases hExec
        exact hLookup

theorem NativeStmtPreservesWord_if_of_eval_preserves
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond :
      ∀ fuel state,
        state[name]! = value →
          ∃ condState condValue,
            EvmYul.Yul.eval fuel cond codeOverride state =
              .ok (condState, condValue) ∧
            condState[name]! = value)
    (hBody : NativeBlockPreservesWord name value body codeOverride) :
    NativeStmtPreservesWord name value (.If cond body) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hCond fuel' state hLookup with
        ⟨condState, condValue, hEval, hCondLookup⟩
      simp [EvmYul.Yul.exec, hEval] at hExec
      by_cases hCondNonzero : condValue ≠ ⟨0⟩
      · simp [hCondNonzero] at hExec
        exact hBody fuel' condState final hCondLookup hExec
      · have hCondZero : condValue = ⟨0⟩ := by
          exact Decidable.not_not.mp hCondNonzero
        simp [hCondZero] at hExec
        cases hExec
        exact hCondLookup

theorem NativeStmtPreservesWord_if_of_eval_preserves_and_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond :
      ∀ fuel state,
        state[name]! = value →
          ∃ condState condValue,
            EvmYul.Yul.eval fuel cond codeOverride state =
              .ok (condState, condValue) ∧
            condState[name]! = value)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames body)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        (name : String) ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeStmtPreservesWord name value (.If cond body) codeOverride :=
  NativeStmtPreservesWord_if_of_eval_preserves name value cond body codeOverride
    hCond
    (NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
      name value body codeOverride hFresh hPreserves)

theorem NativeStmtPreservesWord_if_of_cond_preserves
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond : NativeExprPreservesWord name value cond codeOverride)
    (hBody : NativeBlockPreservesWord name value body codeOverride) :
    NativeStmtPreservesWord name value (.If cond body) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEval : EvmYul.Yul.eval fuel' cond codeOverride state with
      | error err =>
          simp [hEval] at hExec
      | ok condResult =>
          rcases condResult with ⟨condState, condValue⟩
          have hCondLookup : condState[name]! = value :=
            hCond fuel' state condState condValue hLookup hEval
          simp [hEval] at hExec
          by_cases hCondNonzero : condValue ≠ ⟨0⟩
          · simp [hCondNonzero] at hExec
            exact hBody fuel' condState final hCondLookup hExec
          · have hCondZero : condValue = ⟨0⟩ :=
              Decidable.not_not.mp hCondNonzero
            simp [hCondZero] at hExec
            cases hExec
            exact hCondLookup

theorem NativeStmtPreservesWord_if_of_cond_preserves_and_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond : NativeExprPreservesWord name value cond codeOverride)
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames body)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        (name : String) ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeStmtPreservesWord name value (.If cond body) codeOverride :=
  NativeStmtPreservesWord_if_of_cond_preserves name value cond body codeOverride
    hCond
    (NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
      name value body codeOverride hFresh hPreserves)

/-- `_revived` mirror of `NativeStmtPreservesWord_if_of_cond_preserves` using a
condition-state-preservation premise stated via `reviveJump` (instead of OLD-form
`NativeExprPreservesWord` which is unsound on Checkpoint inputs — see memory
`yul-state-lookup-bracket-vs-lookup`).

The premise `hCondReviveJump` is per-condition; for the dispatcher's
`lt(calldatasize, k)` and `callvalue` guards on Ok input, it follows from
`eval_lowerExprNative_*_ok_fuel` (eval returns the same state). -/
theorem NativeStmtPreservesWord_revived_if_of_cond_preserves_reviveJump
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCondReviveJump :
      ∀ fuel state final v,
        EvmYul.Yul.eval fuel cond codeOverride state = .ok (final, v) →
          final.reviveJump = state.reviveJump)
    (hBody : NativeBlockPreservesWord_revived name value body codeOverride) :
    NativeStmtPreservesWord_revived name value (.If cond body) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEval : EvmYul.Yul.eval fuel' cond codeOverride state with
      | error err =>
          simp [hEval] at hExec
      | ok condResult =>
          rcases condResult with ⟨condState, condValue⟩
          have hReviveEq : condState.reviveJump = state.reviveJump :=
            hCondReviveJump fuel' state condState condValue hEval
          have hCondLookup : condState.reviveJump[name]! = value := by
            rw [hReviveEq]; exact hLookup
          simp [hEval] at hExec
          by_cases hCondNonzero : condValue ≠ ⟨0⟩
          · simp [hCondNonzero] at hExec
            exact hBody fuel' condState final hCondLookup hExec
          · have hCondZero : condValue = ⟨0⟩ :=
              Decidable.not_not.mp hCondNonzero
            simp [hCondZero] at hExec
            cases hExec
            exact hCondLookup

theorem nativeSwitchBranchFold_ok_preserves_word
    (name : EvmYul.Identifier)
    (value cond : EvmYul.Literal)
    (branches :
      List (EvmYul.Literal × Except EvmYul.Yul.Exception EvmYul.Yul.State))
    (defaultState final : EvmYul.Yul.State)
    (hBranches :
      ∀ tag branchState, (tag, .ok branchState) ∈ branches →
        branchState[name]! = value)
    (hDefault : defaultState[name]! = value)
    (hFold :
      List.foldr
        (fun (valᵢ, sᵢ) s => if valᵢ = cond then sᵢ else s)
        (.ok defaultState) branches = .ok final) :
    final[name]! = value := by
  induction branches with
  | nil =>
      simp at hFold
      cases hFold
      exact hDefault
  | cons head tail ih =>
      rcases head with ⟨tag, result⟩
      by_cases hEq : tag = cond
      · simp [hEq] at hFold
        cases result with
        | error err =>
            simp at hFold
        | ok branchState =>
            have hBranch : branchState[name]! = value :=
              hBranches tag branchState (by simp)
            cases hFold
            exact hBranch
      · simp [hEq] at hFold
        exact ih
          (by
            intro tag' branchState hMem
            exact hBranches tag' branchState (by simp [hMem]))
          hFold

theorem execSwitchCases_ok_branch_preserves_word
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (cases : List (EvmYul.Literal × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCases : ∀ tag body, (tag, body) ∈ cases → NativeBlockPreservesWord name value body codeOverride) :
    ∀ fuel state branches, state[name]! = value → EvmYul.Yul.execSwitchCases fuel codeOverride state cases = .ok branches →
      ∀ tag branchState, (tag, .ok branchState) ∈ branches → branchState[name]! = value := by
  induction cases with
  | nil =>
      intro fuel state branches _ hExec tag branchState hMem
      simp [EvmYul.Yul.execSwitchCases] at hExec; subst branches; simp at hMem
  | cons head tail ih =>
      intro fuel state branches hLookup hExec tag branchState hMem
      rcases head with ⟨headTag, headBody⟩
      have hTailCases : ∀ tag' body', (tag', body') ∈ tail →
          NativeBlockPreservesWord name value body' codeOverride := by
        intro tag' body' hTailMem; exact hCases tag' body' (by simp [hTailMem])
      cases fuel with
      | zero => simp [EvmYul.Yul.execSwitchCases] at hExec
      | succ fuel' =>
          cases hHead :
              EvmYul.Yul.exec fuel' (.Block headBody) codeOverride state with
          | error err =>
              cases err <;>
                cases hTail :
                    EvmYul.Yul.execSwitchCases fuel' codeOverride state tail with
                | error tailErr =>
                    simp [EvmYul.Yul.execSwitchCases, hHead, hTail] at hExec
                | ok tailBranches =>
                    simp [EvmYul.Yul.execSwitchCases, hHead, hTail] at hExec
                    subst branches
                    simp at hMem
                    exact ih hTailCases fuel' state tailBranches hLookup hTail
                      tag branchState hMem
          | ok headState =>
              cases hTail :
                  EvmYul.Yul.execSwitchCases fuel' codeOverride state tail with
              | error tailErr =>
                  simp [EvmYul.Yul.execSwitchCases, hHead, hTail] at hExec
              | ok tailBranches =>
                  simp [EvmYul.Yul.execSwitchCases, hHead, hTail] at hExec
                  subst branches
                  simp at hMem
                  rcases hMem with hMem | hMem
                  · rcases hMem with ⟨rfl, rfl⟩
                    exact hCases tag headBody (by simp)
                      fuel' state branchState hLookup hHead
                  · exact ih hTailCases fuel' state tailBranches hLookup hTail
                      tag branchState hMem

theorem NativeStmtPreservesWord_switch_of_eval_preserves
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (cases : List (EvmYul.Literal × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond :
      ∀ fuel state,
        state[name]! = value →
          ∃ condState condValue,
            EvmYul.Yul.eval fuel cond codeOverride state =
              .ok (condState, condValue) ∧
            condState[name]! = value)
    (hCases : ∀ tag body, (tag, body) ∈ cases →
      NativeBlockPreservesWord name value body codeOverride)
    (hDefault :
      NativeBlockPreservesWord name value defaultBody codeOverride) :
    NativeStmtPreservesWord name value (.Switch cond cases defaultBody)
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hCond fuel' state hLookup with
        ⟨condState, condValue, hEval, hCondLookup⟩
      simp [EvmYul.Yul.exec, hEval] at hExec
      cases hSwitch :
          EvmYul.Yul.execSwitchCases fuel' codeOverride condState cases with
      | error err =>
          simp [hSwitch] at hExec
      | ok branches =>
          cases hDefaultExec :
              EvmYul.Yul.exec fuel' (.Block defaultBody) codeOverride
                condState with
          | error err =>
              simp [hSwitch, hDefaultExec] at hExec
          | ok defaultState =>
              simp [hSwitch, hDefaultExec] at hExec
              exact nativeSwitchBranchFold_ok_preserves_word name value
                condValue branches defaultState final
                (execSwitchCases_ok_branch_preserves_word name value cases
                  codeOverride hCases fuel' condState branches hCondLookup
                  hSwitch)
                (hDefault fuel' condState defaultState hCondLookup
                  hDefaultExec)
                hExec

theorem NativeStmtPreservesWord_switch_of_cond_preserves
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (cases : List (EvmYul.Literal × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond : NativeExprPreservesWord name value cond codeOverride)
    (hCases : ∀ tag body, (tag, body) ∈ cases →
      NativeBlockPreservesWord name value body codeOverride)
    (hDefault :
      NativeBlockPreservesWord name value defaultBody codeOverride) :
    NativeStmtPreservesWord name value (.Switch cond cases defaultBody)
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEval : EvmYul.Yul.eval fuel' cond codeOverride state with
      | error err =>
          simp [hEval] at hExec
      | ok condResult =>
          rcases condResult with ⟨condState, condValue⟩
          have hCondLookup : condState[name]! = value :=
            hCond fuel' state condState condValue hLookup hEval
          cases hSwitch :
              EvmYul.Yul.execSwitchCases fuel' codeOverride condState cases with
          | error err =>
              simp [hEval, hSwitch] at hExec
          | ok branches =>
              cases hDefaultExec :
                  EvmYul.Yul.exec fuel' (.Block defaultBody) codeOverride
                    condState with
              | error err =>
                  simp [hEval, hSwitch, hDefaultExec] at hExec
              | ok defaultState =>
                  simp [hEval, hSwitch, hDefaultExec] at hExec
                  exact nativeSwitchBranchFold_ok_preserves_word name value
                    condValue branches defaultState final
                    (execSwitchCases_ok_branch_preserves_word name value cases
                      codeOverride hCases fuel' condState branches hCondLookup
                      hSwitch)
                    (hDefault fuel' condState defaultState hCondLookup
                      hDefaultExec)
                    hExec

theorem NativeStmtPreservesWord_switch_of_cond_preserves_and_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (cases : List (EvmYul.Literal × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond : NativeExprPreservesWord name value cond codeOverride)
    (hCasesFresh : ∀ tag body, (tag, body) ∈ cases →
      (name : String) ∉ Backends.nativeStmtsWriteNames body)
    (hDefaultFresh : (name : String) ∉ Backends.nativeStmtsWriteNames defaultBody)
    (hPreserves :
      ∀ stmt, (name : String) ∉ Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord name value stmt codeOverride) :
    NativeStmtPreservesWord name value (.Switch cond cases defaultBody)
      codeOverride :=
  NativeStmtPreservesWord_switch_of_cond_preserves name value cond cases
    defaultBody codeOverride hCond
    (by
      intro tag body hMem
      exact NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
        name value body codeOverride (hCasesFresh tag body hMem)
        (by intro stmt _ hFresh; exact hPreserves stmt hFresh))
    (NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
      name value defaultBody codeOverride hDefaultFresh
      (by intro stmt _ hFresh; exact hPreserves stmt hFresh))

theorem NativeStmtPreservesWord_switch_of_eval_preserves_and_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (cases : List (EvmYul.Literal × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond :
      ∀ fuel state,
        state[name]! = value →
          ∃ condState condValue,
            EvmYul.Yul.eval fuel cond codeOverride state =
              .ok (condState, condValue) ∧
            condState[name]! = value)
    (hCasesFresh : ∀ tag body, (tag, body) ∈ cases →
      (name : String) ∉ Backends.nativeStmtsWriteNames body)
    (hDefaultFresh : (name : String) ∉ Backends.nativeStmtsWriteNames defaultBody)
    (hPreserves :
      ∀ stmt, (name : String) ∉ Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord name value stmt codeOverride) :
    NativeStmtPreservesWord name value (.Switch cond cases defaultBody)
      codeOverride :=
  NativeStmtPreservesWord_switch_of_eval_preserves name value cond cases
    defaultBody codeOverride hCond
    (by
      intro tag body hMem
      exact NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
        name value body codeOverride (hCasesFresh tag body hMem)
        (by intro stmt _ hFresh; exact hPreserves stmt hFresh))
    (NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
      name value defaultBody codeOverride hDefaultFresh
      (by intro stmt _ hFresh; exact hPreserves stmt hFresh))

theorem NativeStmtPreservesWord_lowerAssignNative_lit_of_ne
    (name target : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (assigned : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.lit assigned)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [Backends.lowerAssignNative, Backends.lowerExprNative] at hExec
      cases hExec
      rw [state_getElem_insert_of_ne state name target _ hne]
      exact hLookup

theorem NativeStmtPreservesWord_lowerAssignNative_hex_of_ne
    (name target : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (assigned : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.hex assigned)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [Backends.lowerAssignNative, Backends.lowerExprNative] at hExec
      cases hExec
      rw [state_getElem_insert_of_ne state name target
        (EvmYul.UInt256.ofNat assigned) hne]
      exact hLookup

theorem NativeStmtPreservesWord_lowerAssignNative_ident_of_ne
    (name target source : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.ident source)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [Backends.lowerAssignNative, Backends.lowerExprNative,
        EvmYul.Yul.exec] at hExec
      cases hExec
      rw [state_getElem_insert_of_ne state name target _ hne]
      exact hLookup

theorem NativeStmtPreservesWord_lowerAssignNative_str_of_ne
    (name target source : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.str source)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [Backends.lowerAssignNative, Backends.lowerExprNative,
        EvmYul.Yul.exec] at hExec
      cases hExec
      rw [state_getElem_insert_of_ne state name target _ hne]
      exact hLookup

theorem NativeStmtPreservesWord_let_none_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected (.Let vars none) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hExec
      rw [state_getElem_foldr_insert_zero_of_not_mem state name vars hnot]
      exact hLookup

theorem NativeStmtPreservesWord_let_var_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (.Var identifier))) codeOverride := by
  intro fuel state final hLookup hExec
  rcases List.exists_cons_of_ne_nil hvars with ⟨head, tail, rfl⟩
  simp at hnot
  rcases hnot with ⟨hneq, _⟩
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hExec
      rw [state_getElem_insert_of_ne state name head state[identifier]! hneq]
      exact hLookup

theorem NativeStmtPreservesWord_let_lit_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (literal : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (.Lit literal))) codeOverride := by
  intro fuel state final hLookup hExec
  rcases List.exists_cons_of_ne_nil hvars with ⟨head, tail, rfl⟩
  simp at hnot
  rcases hnot with ⟨hneq, _⟩
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hExec
      rw [state_getElem_insert_of_ne state name head literal hneq]
      exact hLookup

theorem NativeStmtPreservesWord_let_lowerExprNative_lit_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (literal : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.lit literal))))
      codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeStmtPreservesWord_let_lit_of_not_mem name expected vars
      (EvmYul.UInt256.ofNat literal) codeOverride hvars hnot

theorem NativeStmtPreservesWord_let_lowerExprNative_hex_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (literal : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.hex literal))))
      codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeStmtPreservesWord_let_lit_of_not_mem name expected vars
      (EvmYul.UInt256.ofNat literal) codeOverride hvars hnot

theorem NativeStmtPreservesWord_let_lowerExprNative_str_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.str identifier))))
      codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeStmtPreservesWord_let_var_of_not_mem name expected vars identifier
      codeOverride hvars hnot

theorem NativeStmtPreservesWord_let_lowerExprNative_ident_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.ident identifier))))
      codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeStmtPreservesWord_let_var_of_not_mem name expected vars identifier
      codeOverride hvars hnot

theorem NativeStmtPreservesWord_let_prim_of_evalArgs_primCall_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier) (prim : EvmYul.Yul.Ast.PrimOp)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hArgs :
      ∀ fuel state argState values, state[name]! = expected →
          EvmYul.Yul.evalArgs fuel args.reverse codeOverride state = .ok (argState, values) →
          argState[name]! = expected)
    (hPrim :
      ∀ fuel state values primState rets, state[name]! = expected →
          EvmYul.Yul.primCall fuel state prim values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected (.Let vars (some (.Call (Sum.inl prim) args))) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEvalArgs :
          EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          simp [hEvalArgs, EvmYul.Yul.reverse',
            EvmYul.Yul.execPrimCall] at hExec
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          simp [hEvalArgs, EvmYul.Yul.reverse',
            EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
          cases hPrimCall :
              EvmYul.Yul.primCall fuel' argState prim values.reverse with
          | error err =>
              simp [hPrimCall] at hExec
          | ok primResult =>
              rcases primResult with ⟨primState, rets⟩
              simp [hPrimCall] at hExec
              cases hExec
              have hPrimLookup : primState[name]! = expected :=
                hPrim fuel' argState values.reverse primState rets hArgLookup
                  hPrimCall
              rw [state_getElem_multifill_of_not_mem primState name vars rets
                hnot]
              exact hPrimLookup

theorem NativeStmtPreservesWord_let_user_of_evalArgs_call_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal) (vars : List EvmYul.Identifier)
    (functionName : EvmYul.Yul.Ast.YulFunctionName) (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hArgs :
      ∀ fuel state argState values, state[name]! = expected → EvmYul.Yul.evalArgs fuel args.reverse codeOverride state = .ok (argState, values) → argState[name]! = expected)
    (hCall :
      ∀ fuel state values callState rets, state[name]! = expected → EvmYul.Yul.call fuel values (some functionName) codeOverride state = .ok (callState, rets) → callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (.Call (Sum.inr functionName) args))) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEvalArgs :
          EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall] at hExec
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          cases fuel' with
          | zero =>
              simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall]
                at hExec
          | succ callFuel =>
              cases hUserCall :
                  EvmYul.Yul.call callFuel values.reverse (some functionName)
                    codeOverride argState with
              | error err =>
                  simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall, hUserCall,
                    EvmYul.Yul.multifill'] at hExec
              | ok callResult =>
                  rcases callResult with ⟨callState, rets⟩
                  simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall, hUserCall,
                    EvmYul.Yul.multifill'] at hExec
                  cases hExec
                  have hCallLookup : callState[name]! = expected :=
                    hCall callFuel argState values.reverse callState rets
                      hArgLookup hUserCall
                  rw [state_getElem_multifill_of_not_mem callState name vars rets hnot]
                  exact hCallLookup

theorem NativeStmtPreservesWord_let_prim_of_nativeEvalArgs_primCall_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier) (prim : EvmYul.Yul.Ast.PrimOp)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hPrim :
      ∀ fuel state values primState rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state prim values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (.Call (Sum.inl prim) args))) codeOverride :=
  NativeStmtPreservesWord_let_prim_of_evalArgs_primCall_preserves
    name expected vars prim args codeOverride hnot hArgs hPrim

theorem NativeStmtPreservesWord_let_user_of_nativeEvalArgs_call_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hCall :
      ∀ fuel state values callState rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some functionName) codeOverride state =
            .ok (callState, rets) →
          callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (.Call (Sum.inr functionName) args))) codeOverride :=
  NativeStmtPreservesWord_let_user_of_evalArgs_call_preserves
    name expected vars functionName args codeOverride hnot hArgs hCall

theorem NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hPrim :
      ∀ fuel state values primState rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.call func args))))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp func args op hOp]
  exact NativeStmtPreservesWord_let_prim_of_evalArgs_primCall_preserves
    name expected vars op (args.map Backends.lowerExprNative) codeOverride
    hnot hArgs hPrim

theorem NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hCall :
      ∀ fuel state values callState rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (callState, rets) →
          callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.call func args))))
      codeOverride := by
  rw [Backends.lowerExprNative_call_userFunction func args hOp]
  exact NativeStmtPreservesWord_let_user_of_evalArgs_call_preserves
    name expected vars func (args.map Backends.lowerExprNative) codeOverride
    hnot hArgs hCall

theorem NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hPrim :
      ∀ fuel state values primState rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.call func args))))
      codeOverride :=
  NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    name func expected vars args op codeOverride hnot hOp hArgs hPrim

theorem NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hCall :
      ∀ fuel state values callState rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (callState, rets) →
          callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.call func args))))
      codeOverride :=
  NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    name func expected vars args codeOverride hnot hOp hArgs hCall

theorem NativeStmtPreservesWord_let_lowerExprNative_mappingSlot_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (args : List YulExpr)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hnot : name ∉ vars)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse)
        (some
          { dispatcher := dispatcher
            functions := ((∅ : NativeFunctionMap).insert
              "mappingSlot" nativeMappingSlotFunctionDefinition) })) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.call "mappingSlot" args))))
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
  NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves
    name "mappingSlot" expected vars args
    (some
      { dispatcher := dispatcher
        functions := ((∅ : NativeFunctionMap).insert
          "mappingSlot" nativeMappingSlotFunctionDefinition) })
    hnot (by rfl) hArgs
    (by
      intro fuel state values callState rets hLookup hCall
      exact
        native_mappingSlot_call_preserves_lookup_state name expected fuel
          values dispatcher state callState rets hLookup hCall)

theorem NativeStmtPreservesWord_lowerAssignNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    (name target func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hPrim :
      ∀ fuel state values primState rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.call func args)) codeOverride := by
  rw [Backends.lowerAssignNative,
    Backends.lowerExprNative_call_runtimePrimOp func args op hOp]
  exact NativeStmtPreservesWord_let_prim_of_evalArgs_primCall_preserves
    name expected [target] op (args.map Backends.lowerExprNative) codeOverride
    (by simp [hne]) hArgs hPrim

theorem NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_evalArgs_call_preserves
    (name target func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hCall :
      ∀ fuel state values callState rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (callState, rets) →
          callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.call func args)) codeOverride := by
  rw [Backends.lowerAssignNative,
    Backends.lowerExprNative_call_userFunction func args hOp]
  exact NativeStmtPreservesWord_let_user_of_evalArgs_call_preserves
    name expected [target] func (args.map Backends.lowerExprNative) codeOverride
    (by simp [hne]) hArgs hCall

theorem NativeStmtPreservesWord_lowerAssignNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
    (name target func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hPrim :
      ∀ fuel state values primState rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.call func args)) codeOverride :=
  NativeStmtPreservesWord_lowerAssignNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    name target func expected args op codeOverride hne hOp hArgs hPrim

theorem NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_nativeEvalArgs_call_preserves
    (name target func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hCall :
      ∀ fuel state values callState rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (callState, rets) →
          callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.call func args)) codeOverride :=
  NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_evalArgs_call_preserves
    name target func expected args codeOverride hne hOp hArgs hCall

theorem NativeStmtPreservesWord_let_lowerExprNative_of_mappingFreeBridgedExpr
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (target : EvmYul.Identifier)
    (value : YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target)
    (hValue : NativeMappingFreeBridgedExpr value) :
    NativeStmtPreservesWord name expected
      (.Let [target] (some (Backends.lowerExprNative value))) codeOverride := by
  cases value with
  | lit n =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_lit_of_not_mem
          name expected [target] n codeOverride (by simp) (by simpa using hne)
  | hex n =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_hex_of_not_mem
          name expected [target] n codeOverride (by simp) (by simpa using hne)
  | str s =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_str_of_not_mem
          name expected [target] s codeOverride (by simp) (by simpa using hne)
  | ident ident =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_ident_of_not_mem
          name expected [target] ident codeOverride (by simp) (by simpa using hne)
  | call func args =>
      cases hValue with
      | call _ _ hName hNoMapping hArgs =>
          have hNativeArgs :
              NativeEvalArgsPreservesWord name expected
                ((args.map Backends.lowerExprNative).reverse) codeOverride :=
            NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
              name expected args codeOverride hArgs
          cases hOp : Backends.lookupRuntimePrimOp func with
          | some op =>
              exact
                NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
                  name func expected [target] args op codeOverride
                  (by simp [hne]) hOp hNativeArgs
                  (NativePrimCallPreservesWord_of_allowed_lookupRuntimePrimOp
                    name func expected op hName hOp)
          | none =>
              exfalso
              exact lookupRuntimePrimOp_ne_none_of_allowed_of_ne_mappingSlot
                func hName hNoMapping hOp

theorem NativeStmtPreservesWord_letMany_lowerExprNative_of_mappingFreeBridgedExpr
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (value : YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars)
    (hValue : NativeMappingFreeBridgedExpr value) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative value))) codeOverride := by
  cases value with
  | lit n =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_lit_of_not_mem
          name expected vars n codeOverride hvars hnot
  | hex n =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_hex_of_not_mem
          name expected vars n codeOverride hvars hnot
  | str s =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_str_of_not_mem
          name expected vars s codeOverride hvars hnot
  | ident ident =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_ident_of_not_mem
          name expected vars ident codeOverride hvars hnot
  | call func args =>
      cases hValue with
      | call _ _ hName hNoMapping hArgs =>
          have hNativeArgs :
              NativeEvalArgsPreservesWord name expected
                ((args.map Backends.lowerExprNative).reverse) codeOverride :=
            NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
              name expected args codeOverride hArgs
          cases hOp : Backends.lookupRuntimePrimOp func with
          | some op =>
              exact
                NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
                  name func expected vars args op codeOverride hnot hOp
                  hNativeArgs
                  (NativePrimCallPreservesWord_of_allowed_lookupRuntimePrimOp
                    name func expected op hName hOp)
          | none =>
              exfalso
              exact lookupRuntimePrimOp_ne_none_of_allowed_of_ne_mappingSlot
                func hName hNoMapping hOp

theorem NativeStmtPreservesWord_lowerAssignNative_of_mappingFreeBridgedExpr
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (target : EvmYul.Identifier)
    (value : YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target)
    (hValue : NativeMappingFreeBridgedExpr value) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target value) codeOverride := by
  simpa [Backends.lowerAssignNative] using
    NativeStmtPreservesWord_let_lowerExprNative_of_mappingFreeBridgedExpr
      name expected target value codeOverride hne hValue

theorem NativeStmtPreservesWord_lowerAssignNative_mappingSlot_of_nativeEvalArgs
    (name target : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hne : name ≠ target)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse)
        (some
          { dispatcher := dispatcher
            functions := ((∅ : NativeFunctionMap).insert
              "mappingSlot" nativeMappingSlotFunctionDefinition) })) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.call "mappingSlot" args))
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
  NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_nativeEvalArgs_call_preserves
    name target "mappingSlot" expected args
    (some
      { dispatcher := dispatcher
        functions := ((∅ : NativeFunctionMap).insert
          "mappingSlot" nativeMappingSlotFunctionDefinition) })
    hne (by rfl) hArgs
    (by
      intro fuel state values callState rets hLookup hCall
      exact
        native_mappingSlot_call_preserves_lookup_state name expected fuel
          values dispatcher state callState rets hLookup hCall)

theorem NativeStmtPreservesWord_let_lowerExprNative_of_bridgedExpr_mappingContract
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (target : EvmYul.Identifier)
    (value : YulExpr)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hne : name ≠ target)
    (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value) :
    NativeStmtPreservesWord name expected
      (.Let [target] (some (Backends.lowerExprNative value)))
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  cases value with
  | lit n =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_lit_of_not_mem
          name expected [target] n _ (by simp) (by simpa using hne)
  | hex n =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_hex_of_not_mem
          name expected [target] n _ (by simp) (by simpa using hne)
  | str s =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_str_of_not_mem
          name expected [target] s _ (by simp) (by simpa using hne)
  | ident ident =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_ident_of_not_mem
          name expected [target] ident _ (by simp) (by simpa using hne)
  | call func args =>
      cases hValue with
      | call _ _ hName hArgs =>
          have hNativeArgs :
              NativeEvalArgsPreservesWord name expected
                ((args.map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
            NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
              name expected args dispatcher hArgs
          by_cases hMapping : func = "mappingSlot"
          · subst func
            exact
              NativeStmtPreservesWord_let_lowerExprNative_mappingSlot_of_nativeEvalArgs
                name expected [target] args dispatcher (by simp [hne])
                hNativeArgs
          · cases hOp : Backends.lookupRuntimePrimOp func with
            | some op =>
                exact
                  NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
                    name func expected [target] args op _ (by simp [hne]) hOp
                    hNativeArgs
                    (NativePrimCallPreservesWord_of_allowed_lookupRuntimePrimOp
                      name func expected op hName hOp)
            | none =>
                exfalso
                exact lookupRuntimePrimOp_ne_none_of_allowed_of_ne_mappingSlot
                  func hName hMapping hOp

theorem NativeStmtPreservesWord_letMany_lowerExprNative_of_bridgedExpr_mappingContract
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (value : YulExpr)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars)
    (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative value)))
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  cases value with
  | lit n =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_lit_of_not_mem
          name expected vars n _ hvars hnot
  | hex n =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_hex_of_not_mem
          name expected vars n _ hvars hnot
  | str s =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_str_of_not_mem
          name expected vars s _ hvars hnot
  | ident ident =>
      exact
        NativeStmtPreservesWord_let_lowerExprNative_ident_of_not_mem
          name expected vars ident _ hvars hnot
  | call func args =>
      cases hValue with
      | call _ _ hName hArgs =>
          have hNativeArgs :
              NativeEvalArgsPreservesWord name expected
                ((args.map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
            NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
              name expected args dispatcher hArgs
          by_cases hMapping : func = "mappingSlot"
          · subst func
            exact
              NativeStmtPreservesWord_let_lowerExprNative_mappingSlot_of_nativeEvalArgs
                name expected vars args dispatcher hnot hNativeArgs
          · cases hOp : Backends.lookupRuntimePrimOp func with
            | some op =>
                exact
                  NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
                    name func expected vars args op _ hnot hOp
                    hNativeArgs
                    (NativePrimCallPreservesWord_of_allowed_lookupRuntimePrimOp
                      name func expected op hName hOp)
            | none =>
                exfalso
                exact lookupRuntimePrimOp_ne_none_of_allowed_of_ne_mappingSlot
                  func hName hMapping hOp

theorem NativeStmtPreservesWord_lowerAssignNative_of_bridgedExpr_mappingContract
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (target : EvmYul.Identifier)
    (value : YulExpr)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hne : name ≠ target)
    (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target value)
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  simpa [Backends.lowerAssignNative] using
    NativeStmtPreservesWord_let_lowerExprNative_of_bridgedExpr_mappingContract
      name expected target value dispatcher hne hValue

theorem NativeStmtPreservesWord_empty_block
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeStmtPreservesWord name expected (.Block []) codeOverride :=
  NativeStmtPreservesWord_block name expected [] codeOverride
    (NativeBlockPreservesWord_nil name expected codeOverride)

/-! ## Leave preservation in the revived form

The standard `NativeStmtPreservesWord_leave` is structurally false because
`exec fuel .Leave _ (Ok shared store) = Checkpoint (.Leave shared store)`, and
the lookup on Checkpoint reads the empty default store. The `_revived`
variant looks up through `reviveJump`, which revives Checkpoint to its inner
store, allowing the matched flag to be preserved across the Leave. -/
theorem NativeStmtPreservesWord_revived_leave
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeStmtPreservesWord_revived name value .Leave codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero => simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases state with
      | Ok shared store =>
          subst final
          simp [EvmYul.Yul.State.setLeave, reviveJump_Leave_eq]
          simpa [reviveJump_Ok_eq] using hLookup
      | OutOfFuel =>
          subst final
          simpa [EvmYul.Yul.State.setLeave] using hLookup
      | Checkpoint jump =>
          subst final
          simpa [EvmYul.Yul.State.setLeave] using hLookup

/-- Empty-block preservation in the `_revived` form. `exec _ (.Block []) _ s`
returns `s` unchanged, so the conclusion is just the hypothesis. -/
theorem NativeStmtPreservesWord_revived_empty_block
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeStmtPreservesWord_revived name expected (.Block []) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero => simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      subst hExec
      exact hLookup

/-- `_revived` form for the `.Block [.Leave]` shape produced by E4's
lowering of an IR `[.block [.leave]]` body. Composes the `_revived` block
wrapper with the `_revived` singleton + leave lemma. -/
theorem NativeStmtPreservesWord_revived_block_leave
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeStmtPreservesWord_revived name value (.Block [.Leave]) codeOverride :=
  NativeStmtPreservesWord_revived_block name value [.Leave] codeOverride
    (NativeBlockPreservesWord_revived_singleton name value .Leave codeOverride
      (NativeStmtPreservesWord_revived_leave name value codeOverride))

/-- `_revived` block preservation for the body shape `[.Block [], .Leave]` —
the lowered form of an IR `[.block [], .leave]` body (F2's body shape). Used
by the future label-prefix lift `ExecBridgeAtFuelRevivedLeaveAware.of_leave_body_with_label_prefix`. -/
theorem NativeBlockPreservesWord_revived_block_empty_then_leave
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeBlockPreservesWord_revived name value [.Block [], .Leave]
      codeOverride :=
  NativeBlockPreservesWord_revived_cons name value (.Block []) [.Leave]
    codeOverride
    (NativeStmtPreservesWord_revived_empty_block name value codeOverride)
    (NativeBlockPreservesWord_revived_singleton name value .Leave codeOverride
      (NativeStmtPreservesWord_revived_leave name value codeOverride))

/-- Generic vacuity helper: if a `.Block` body's exec never produces an
`.ok` result, then `_revived` preservation holds trivially (the implication's
premise is unsatisfiable).

Useful for halt-style bodies whose exec always returns `.error YulHalt`
(stop / return / revert), where `_revived` preservation is vacuous. The
counterpart for the OLD-form `NativeBlockPreservesWord` follows by the same
argument; see `NativeBlockPreservesWord_of_never_ok` below. -/
theorem NativeBlockPreservesWord_revived_of_never_ok
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hNeverOk :
      ∀ fuel state final,
        EvmYul.Yul.exec fuel (.Block body) codeOverride state ≠ .ok final) :
    NativeBlockPreservesWord_revived name value body codeOverride := by
  intro fuel state final _hRevive hExec
  exact absurd hExec (hNeverOk fuel state final)

/-- OLD-form counterpart of `NativeBlockPreservesWord_revived_of_never_ok`. -/
theorem NativeBlockPreservesWord_of_never_ok
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hNeverOk :
      ∀ fuel state final,
        EvmYul.Yul.exec fuel (.Block body) codeOverride state ≠ .ok final) :
    NativeBlockPreservesWord name value body codeOverride := by
  intro fuel state final _hLookup hExec
  exact absurd hExec (hNeverOk fuel state final)

/-- Helper for `NativeBlockPreservesWord_revived_nativeRevertZeroZero`: for
fuel < 7, `exec fuel (.Block [revert]) state` is structurally not `.ok` — the
fuel runs out before completing the primitive-call unfolding. -/
private theorem exec_block_nativeRevertZeroZero_low_fuel_ne_ok
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State) (fuel : Nat) (hLt : fuel < 7) :
    EvmYul.Yul.exec fuel (.Block [nativeRevertZeroZeroStmt]) codeOverride state
      ≠ .ok final := by
  intro hExec
  match fuel, hLt, hExec with
  | 0, _, hExec => simp [EvmYul.Yul.exec] at hExec
  | 1, _, hExec => simp [EvmYul.Yul.exec, nativeRevertZeroZeroStmt] at hExec
  | 2, _, hExec =>
      simp [EvmYul.Yul.exec, nativeRevertZeroZeroStmt, EvmYul.Yul.eval,
        EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
        EvmYul.Yul.reverse', EvmYul.Yul.cons'] at hExec
  | 3, _, hExec =>
      simp [EvmYul.Yul.exec, nativeRevertZeroZeroStmt, EvmYul.Yul.eval,
        EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
        EvmYul.Yul.reverse', EvmYul.Yul.cons'] at hExec
  | 4, _, hExec =>
      simp [EvmYul.Yul.exec, nativeRevertZeroZeroStmt, EvmYul.Yul.eval,
        EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
        EvmYul.Yul.reverse', EvmYul.Yul.cons'] at hExec
  | 5, _, hExec =>
      simp [EvmYul.Yul.exec, nativeRevertZeroZeroStmt, EvmYul.Yul.eval,
        EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
        EvmYul.Yul.reverse', EvmYul.Yul.cons'] at hExec
  | 6, _, hExec =>
      simp [EvmYul.Yul.exec, nativeRevertZeroZeroStmt, EvmYul.Yul.eval,
        EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
        EvmYul.Yul.reverse', EvmYul.Yul.cons'] at hExec

/-- `_revived` block preservation for the singleton revert body
`[nativeRevertZeroZeroStmt]`. Proved via the vacuity helper: revert always
errors, so `exec ... = .ok final` is structurally unsatisfiable.

This is the first leaf of the parallel `_revived` upstream chain needed by
the dispatcher continuation provider — mirror of the OLD-form
`NativeBlockPreservesWord_nativeRevertZeroZero` (in EndToEnd.lean) without
going through the (currently missing) `_revived` primitive call chain. -/
theorem NativeBlockPreservesWord_revived_nativeRevertZeroZero
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeBlockPreservesWord_revived name value
      [nativeRevertZeroZeroStmt] codeOverride := by
  apply NativeBlockPreservesWord_revived_of_never_ok
  intro fuel state final hExec
  by_cases hLt : fuel < 7
  · exact exec_block_nativeRevertZeroZero_low_fuel_ne_ok codeOverride state
      final fuel hLt hExec
  · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 7 := ⟨fuel - 7, by omega⟩
    have hStmt :
        EvmYul.Yul.exec (n + 6) nativeRevertZeroZeroStmt codeOverride state =
          .error EvmYul.Yul.Exception.Revert :=
      exec_revert_zero_zero_error n state codeOverride
    have hBlock :
        EvmYul.Yul.exec (Nat.succ (n + 6)) (.Block [nativeRevertZeroZeroStmt])
          codeOverride state = .error EvmYul.Yul.Exception.Revert :=
      exec_block_cons_error (n + 6) nativeRevertZeroZeroStmt [] codeOverride
        state EvmYul.Yul.Exception.Revert hStmt
    rw [show n + 7 = Nat.succ (n + 6) from rfl, hBlock] at hExec
    cases hExec

/-- `_revived` block preservation for the body shape `[.Block [], .Block [.Leave]]`
— the lowered form of an IR `[.block [], .block [.leave]]` body (F4's body
shape). Used by the future label-prefix lift for the block-leave case. -/
theorem NativeBlockPreservesWord_revived_block_empty_then_block_leave
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeBlockPreservesWord_revived name value
      [.Block [], .Block [.Leave]] codeOverride :=
  NativeBlockPreservesWord_revived_cons name value (.Block [])
    [.Block [.Leave]] codeOverride
    (NativeStmtPreservesWord_revived_empty_block name value codeOverride)
    (NativeBlockPreservesWord_revived_singleton name value (.Block [.Leave])
      codeOverride
      (NativeStmtPreservesWord_revived_block_leave name value codeOverride))

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_comment
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (text : String)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.comment text) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_comment] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact NativeStmtPreservesWord_empty_block name expected _

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_let
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (target : EvmYul.Identifier)
    (value : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.let_ target value) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hne : name ≠ target) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_let] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_let_lowerExprNative_of_bridgedExpr_mappingContract
      name expected target value dispatcher hne hValue

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_let_of_write_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (target : EvmYul.Identifier)
    (value : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.let_ target value) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hFresh : (name : String) ∉ Backends.nativeStmtWriteNames nativeStmt) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_let] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  refine
    NativeStmtPreservesWord_let_lowerExprNative_of_bridgedExpr_mappingContract
      name expected target value dispatcher
      (nativeStmtWriteNames_let_singleton_not_mem_ne name target
        (some (Backends.lowerExprNative value)) hFresh)
      hValue

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_letMany_of_write_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (targets : List EvmYul.Identifier)
    (value : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hTargets : targets ≠ [])
    (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.letMany targets value) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hFresh : (name : String) ∉ Backends.nativeStmtWriteNames nativeStmt) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_letMany] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_letMany_lowerExprNative_of_bridgedExpr_mappingContract
      name expected targets value dispatcher hTargets
      (nativeStmtWriteNames_let_not_mem_vars name targets
        (some (Backends.lowerExprNative value)) hFresh)
      hValue

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_assign
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (target : EvmYul.Identifier)
    (value : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.assign target value) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hne : name ≠ target) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_assign] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_lowerAssignNative_of_bridgedExpr_mappingContract
      name expected target value dispatcher hne hValue

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_assign_of_write_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (target : EvmYul.Identifier)
    (value : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.assign target value) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hFresh : (name : String) ∉ Backends.nativeStmtWriteNames nativeStmt) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_assign] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  refine
    NativeStmtPreservesWord_lowerAssignNative_of_bridgedExpr_mappingContract
      name expected target value dispatcher
      (nativeStmtWriteNames_lowerAssignNative_not_mem_ne name target value hFresh)
      hValue

theorem NativeStmtPreservesWord_exprStmtCall_prim_of_evalArgs_primCall_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (prim : EvmYul.Yul.Ast.PrimOp)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state prim values = .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl prim) args)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEvalArgs :
          EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execPrimCall] at hExec
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execPrimCall,
            EvmYul.Yul.multifill'] at hExec
          cases hPrimCall :
              EvmYul.Yul.primCall fuel' argState prim values.reverse with
          | error err =>
              simp [hPrimCall] at hExec
          | ok primResult =>
              rcases primResult with ⟨primState, rets⟩
              simp [hPrimCall, EvmYul.Yul.State.multifill] at hExec
              cases hExec
              have hPrimLookup : primState[name]! = expected :=
                hPrim fuel' argState values.reverse primState rets hArgLookup
                  hPrimCall
              cases primState <;> simpa using hPrimLookup

theorem NativeStmtPreservesWord_exprStmtCall_user_of_evalArgs_call_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal)
    (functionName : EvmYul.Yul.Ast.YulFunctionName) (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state argState values, state[name]! = expected → EvmYul.Yul.evalArgs fuel args.reverse codeOverride state = .ok (argState, values) → argState[name]! = expected)
    (hCall :
      ∀ fuel state values final rets, state[name]! = expected → EvmYul.Yul.call fuel values (some functionName) codeOverride state = .ok (final, rets) → final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inr functionName) args)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEvalArgs :
          EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall] at hExec
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          cases fuel' with
          | zero =>
              simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall]
                at hExec
          | succ callFuel =>
              cases hUserCall :
                  EvmYul.Yul.call callFuel values.reverse (some functionName)
                    codeOverride argState with
              | error err =>
                  simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall, hUserCall,
                    EvmYul.Yul.multifill'] at hExec
              | ok callResult =>
                  rcases callResult with ⟨callState, rets⟩
                  simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall, hUserCall,
                    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill] at hExec
                  cases hExec
                  have hCallLookup : callState[name]! = expected :=
                    hCall callFuel argState values.reverse callState rets
                      hArgLookup hUserCall
                  cases callState <;> simpa using hCallLookup

theorem NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (prim : EvmYul.Yul.Ast.PrimOp)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state prim values = .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl prim) args)) codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_evalArgs_primCall_preserves
    name expected prim args codeOverride hArgs hPrim

theorem NativeStmtPreservesWord_exprStmtCall_user_of_nativeEvalArgs_call_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hCall :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some functionName) codeOverride state =
            .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inr functionName) args)) codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_user_of_evalArgs_call_preserves
    name expected functionName args codeOverride hArgs hCall

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call func args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp func args op hOp]
  exact NativeStmtPreservesWord_exprStmtCall_prim_of_evalArgs_primCall_preserves
    name expected op (args.map Backends.lowerExprNative) codeOverride hArgs
    hPrim

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hCall :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call func args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_userFunction func args hOp]
  exact NativeStmtPreservesWord_exprStmtCall_user_of_evalArgs_call_preserves
    name expected func (args.map Backends.lowerExprNative) codeOverride hArgs
    hCall

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call func args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    name func expected args op codeOverride hOp hArgs hPrim

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hCall :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call func args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    name func expected args codeOverride hOp hArgs hCall

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mappingSlot_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse)
        (some
          { dispatcher := dispatcher
            functions := ((∅ : NativeFunctionMap).insert
              "mappingSlot" nativeMappingSlotFunctionDefinition) })) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "mappingSlot" args)))
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves
    name "mappingSlot" expected args
    (some
      { dispatcher := dispatcher
        functions := ((∅ : NativeFunctionMap).insert
          "mappingSlot" nativeMappingSlotFunctionDefinition) })
    (by rfl) hArgs
    (by
      intro fuel state values final rets hLookup hCall
      exact
        native_mappingSlot_call_preserves_lookup_state name expected fuel
          values dispatcher state final rets hLookup hCall)

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_call_of_bridgedExpr_mappingContract
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (func : EvmYul.Identifier)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hName : Compiler.Proofs.YulGeneration.Backends.allowedExprCallName func)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call func args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  have hNativeArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse)
        (some
          { dispatcher := dispatcher
            functions := ((∅ : NativeFunctionMap).insert
              "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
    NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
      name expected args dispatcher hArgs
  by_cases hMapping : func = "mappingSlot"
  · subst func
    exact
      NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mappingSlot_of_nativeEvalArgs
        name expected args dispatcher hNativeArgs
  · cases hOp : Backends.lookupRuntimePrimOp func with
    | some op =>
        exact
          NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
            name func expected args op _ hOp hNativeArgs
            (NativePrimCallPreservesWord_of_allowed_lookupRuntimePrimOp
              name func expected op hName hOp)
    | none =>
        exfalso
        exact lookupRuntimePrimOp_ne_none_of_allowed_of_ne_mappingSlot
          func hName hMapping hOp

theorem NativeStmtPreservesWord_exprStmtCall_mstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.MSTORE) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, value, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          rw [primCall_mstore_ok] at hExec
          cases hExec
          rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
          rw [state_getElem_setMachineState]
          exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_mstore_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.MSTORE) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_mstore_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, value, hEval⟩
      exact ⟨argState, offset, value, hEval,
        hArgs fuel state argState [value, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_mstore_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.MSTORE) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.MSTORE args codeOverride hArgs
    (NativePrimCallPreservesWord_mstore_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "mstore" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "mstore" args
    EvmYul.Operation.MSTORE (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_mstore_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "mstore" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, value, hEval⟩
      exact ⟨argState, offset, value, hEval,
        hArgs fuel state argState [value, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "mstore" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "mstore" args
    EvmYul.Operation.MSTORE (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_mstore_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_mstore8_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.MSTORE8) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, value, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          rw [primCall_mstore8_ok] at hExec
          cases hExec
          rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
          rw [state_getElem_setMachineState]
          exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_mstore8_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.MSTORE8) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_mstore8_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, value, hEval⟩
      exact ⟨argState, offset, value, hEval,
        hArgs fuel state argState [value, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_mstore8_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.MSTORE8) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.MSTORE8 args codeOverride hArgs
    (NativePrimCallPreservesWord_mstore8_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "mstore8" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "mstore8" args
    EvmYul.Operation.MSTORE8 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_mstore8_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "mstore8" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, value, hEval⟩
      exact ⟨argState, offset, value, hEval,
        hArgs fuel state argState [value, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "mstore8" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "mstore8" args
    EvmYul.Operation.MSTORE8 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_mstore8_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_sstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, slot]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.SSTORE) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, slot, value, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_sstore_ok primFuel argState slot value hPerm] at hExec
            cases hExec
            rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
            rw [state_getElem_setState]
            exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_sstore_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, slot])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.SSTORE) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_sstore_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, slot, value, hEval⟩
      exact ⟨argState, slot, value, hEval,
        hArgs fuel state argState [value, slot] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_sstore_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.SSTORE) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.SSTORE args codeOverride hArgs
    (NativePrimCallPreservesWord_sstore_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, slot]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "sstore" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "sstore" args
    EvmYul.Operation.SSTORE (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_sstore_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, slot])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "sstore" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, slot, value, hEval⟩
      exact ⟨argState, slot, value, hEval,
        hArgs fuel state argState [value, slot] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "sstore" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "sstore" args
    EvmYul.Operation.SSTORE (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_sstore_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_tstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, slot]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.TSTORE) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, slot, value, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_tstore_ok primFuel argState slot value hPerm] at hExec
            cases hExec
            rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
            rw [state_getElem_setState]
            exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_tstore_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, slot])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.TSTORE) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_tstore_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, slot, value, hEval⟩
      exact ⟨argState, slot, value, hEval,
        hArgs fuel state argState [value, slot] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_tstore_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.TSTORE) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.TSTORE args codeOverride hArgs
    (NativePrimCallPreservesWord_tstore_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, slot]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "tstore" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "tstore" args
    EvmYul.Operation.TSTORE (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_tstore_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, slot])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "tstore" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, slot, value, hEval⟩
      exact ⟨argState, slot, value, hEval,
        hArgs fuel state argState [value, slot] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "tstore" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "tstore" args
    EvmYul.Operation.TSTORE (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_tstore_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart datastart size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, datastart, mstart]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.CALLDATACOPY) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, mstart, datastart, size, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          rw [primCall_calldatacopy_ok] at hExec
          cases hExec
          rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
          rw [state_getElem_setSharedState]
          exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart datastart size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, datastart, mstart])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.CALLDATACOPY) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, mstart, datastart, size, hEval⟩
      exact ⟨argState, mstart, datastart, size, hEval,
        hArgs fuel state argState [size, datastart, mstart] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart datastart size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, datastart, mstart]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "calldatacopy" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "calldatacopy" args
    EvmYul.Operation.CALLDATACOPY (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart datastart size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, datastart, mstart])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "calldatacopy" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, mstart, datastart, size, hEval⟩
      exact ⟨argState, mstart, datastart, size, hEval,
        hArgs fuel state argState [size, datastart, mstart] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart rstart size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, rstart, mstart]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.RETURNDATACOPY) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, mstart, rstart, size, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          rw [primCall_returndatacopy_ok] at hExec
          cases hExec
          rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
          rw [state_getElem_setMachineState]
          exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart rstart size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, rstart, mstart])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.RETURNDATACOPY) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, mstart, rstart, size, hEval⟩
      exact ⟨argState, mstart, rstart, size, hEval,
        hArgs fuel state argState [size, rstart, mstart] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart rstart size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, rstart, mstart]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "returndatacopy" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "returndatacopy" args
    EvmYul.Operation.RETURNDATACOPY (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart rstart size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, rstart, mstart])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "returndatacopy" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, mstart, rstart, size, hEval⟩
      exact ⟨argState, mstart, rstart, size, hEval,
        hArgs fuel state argState [size, rstart, mstart] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.CALLDATACOPY) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.CALLDATACOPY args codeOverride hArgs
    (NativePrimCallPreservesWord_calldatacopy_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "calldatacopy" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "calldatacopy" args
    EvmYul.Operation.CALLDATACOPY (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.RETURNDATACOPY) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.RETURNDATACOPY args codeOverride hArgs
    (NativePrimCallPreservesWord_returndatacopy_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "returndatacopy" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "returndatacopy" args
    EvmYul.Operation.RETURNDATACOPY (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_log0_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG0) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_log0_ok primFuel argState offset size hPerm] at hExec
            cases hExec
            rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
            rw [state_getElem_setSharedState]
            exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_log0_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG0) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_log0_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, hEval⟩
      exact ⟨argState, offset, size, hEval,
        hArgs fuel state argState [size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log0" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log0" args
    EvmYul.Operation.LOG0 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log0_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log0" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, hEval⟩
      exact ⟨argState, offset, size, hEval,
        hArgs fuel state argState [size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_log1_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG1) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, topic0, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_log1_ok primFuel argState offset size topic0 hPerm] at hExec
            cases hExec
            rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
            rw [state_getElem_setSharedState]
            exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_log1_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic0, size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG1) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_log1_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, topic0, hEval⟩
      exact ⟨argState, offset, size, topic0, hEval,
        hArgs fuel state argState [topic0, size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log1" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log1" args
    EvmYul.Operation.LOG1 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log1_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic0, size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log1" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, topic0, hEval⟩
      exact ⟨argState, offset, size, topic0, hEval,
        hArgs fuel state argState [topic0, size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_log2_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG2) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, topic0, topic1, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_log2_ok primFuel argState offset size topic0 topic1 hPerm] at hExec
            cases hExec
            rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
            rw [state_getElem_setSharedState]
            exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_log2_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic1, topic0, size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG2) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_log2_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, topic0, topic1, hEval⟩
      exact ⟨argState, offset, size, topic0, topic1, hEval,
        hArgs fuel state argState [topic1, topic0, size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log2" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log2" args
    EvmYul.Operation.LOG2 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log2_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic1, topic0, size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log2" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, topic0, topic1, hEval⟩
      exact ⟨argState, offset, size, topic0, topic1, hEval,
        hArgs fuel state argState [topic1, topic0, size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_log3_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic2, topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG3) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, topic0, topic1, topic2, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_log3_ok primFuel argState offset size topic0 topic1 topic2 hPerm] at hExec
            cases hExec
            rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
            rw [state_getElem_setSharedState]
            exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_log3_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic2, topic1, topic0, size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG3) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_log3_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, topic0, topic1, topic2, hEval⟩
      exact ⟨argState, offset, size, topic0, topic1, topic2, hEval,
        hArgs fuel state argState [topic2, topic1, topic0, size, offset]
          hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic2, topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log3" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log3" args
    EvmYul.Operation.LOG3 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log3_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic2, topic1, topic0, size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log3" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, topic0, topic1, topic2, hEval⟩
      exact ⟨argState, offset, size, topic0, topic1, topic2, hEval,
        hArgs fuel state argState [topic2, topic1, topic0, size, offset]
          hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_log4_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2 topic3,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic3, topic2, topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG4) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, topic0, topic1, topic2, topic3, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_log4_ok primFuel argState offset size topic0 topic1 topic2 topic3 hPerm] at hExec
            cases hExec
            rw [state_getElem_multifill_of_not_mem _ name [] [] (by simp)]
            rw [state_getElem_setSharedState]
            exact hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_log4_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2 topic3,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic3, topic2, topic1, topic0, size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG4) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_log4_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, topic0, topic1, topic2, topic3, hEval⟩
      exact ⟨argState, offset, size, topic0, topic1, topic2, topic3, hEval,
        hArgs fuel state argState
          [topic3, topic2, topic1, topic0, size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2 topic3,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic3, topic2, topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log4" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log4" args
    EvmYul.Operation.LOG4 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log4_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2 topic3,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic3, topic2, topic1, topic0, size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log4" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, topic0, topic1, topic2, topic3, hEval⟩
      exact ⟨argState, offset, size, topic0, topic1, topic2, topic3, hEval,
        hArgs fuel state argState
          [topic3, topic2, topic1, topic0, size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_log0_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG0) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.LOG0 args codeOverride hArgs
    (NativePrimCallPreservesWord_log0_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log0" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log0" args
    EvmYul.Operation.LOG0 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log0_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_log1_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG1) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.LOG1 args codeOverride hArgs
    (NativePrimCallPreservesWord_log1_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log1" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log1" args
    EvmYul.Operation.LOG1 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log1_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_log2_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG2) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.LOG2 args codeOverride hArgs
    (NativePrimCallPreservesWord_log2_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log2" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log2" args
    EvmYul.Operation.LOG2 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log2_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_log3_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG3) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.LOG3 args codeOverride hArgs
    (NativePrimCallPreservesWord_log3_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log3" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log3" args
    EvmYul.Operation.LOG3 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log3_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_log4_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG4) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.LOG4 args codeOverride hArgs
    (NativePrimCallPreservesWord_log4_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log4" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log4" args
    EvmYul.Operation.LOG4 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log4_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_return_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.RETURN) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, hEval, _hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ returnFuel =>
          rw [primCall_return_ok returnFuel argState offset size] at hExec
          cases hReturn :
              EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmReturn
                argState [offset, size] with
          | error err =>
              simp [hReturn] at hExec
          | ok ret =>
              rcases ret with ⟨returnState, value⟩
              simp [hReturn] at hExec

theorem NativeStmtPreservesWord_exprStmtCall_return_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.RETURN) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_return_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, hEval⟩
      exact ⟨argState, offset, size, hEval,
        hArgs fuel state argState [size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "return" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "return" args
    EvmYul.Operation.RETURN (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_return_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "return" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, hEval⟩
      exact ⟨argState, offset, size, hEval,
        hArgs fuel state argState [size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_return_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.RETURN) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.RETURN args codeOverride hArgs
    (NativePrimCallPreservesWord_return_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "return" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "return" args
    EvmYul.Operation.RETURN (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_return_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_revert_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.REVERT) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, hEval, _hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ revertFuel =>
          rw [primCall_revert_ok revertFuel argState offset size] at hExec
          cases hRevert :
              EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmRevert
                argState [offset, size] with
          | error err =>
              simp [hRevert] at hExec
          | ok ret =>
              rcases ret with ⟨revertState, value⟩
              simp [hRevert] at hExec

theorem NativeStmtPreservesWord_exprStmtCall_revert_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.REVERT) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_revert_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, hEval⟩
      exact ⟨argState, offset, size, hEval,
        hArgs fuel state argState [size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "revert" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "revert" args
    EvmYul.Operation.REVERT (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_revert_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_nativeEvalArgs_and_evalArgs_shape_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, offset])) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "revert" args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_evalArgs_preserves
    name expected args codeOverride
    (by
      intro fuel state hLookup
      rcases hShape fuel state hLookup with
        ⟨argState, offset, size, hEval⟩
      exact ⟨argState, offset, size, hEval,
        hArgs fuel state argState [size, offset] hLookup hEval⟩)

theorem NativeStmtPreservesWord_exprStmtCall_revert_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.REVERT) args))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
    name expected EvmYul.Operation.REVERT args codeOverride hArgs
    (NativePrimCallPreservesWord_revert_values name expected)

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_nativeEvalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "revert" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "revert" args
    EvmYul.Operation.REVERT (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_revert_of_nativeEvalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_stop
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.STOP) []))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall,
            EvmYul.Yul.evalArgs, EvmYul.Yul.reverse'] at hExec
      | succ stopFuel =>
          simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall,
            EvmYul.Yul.evalArgs, EvmYul.Yul.reverse'] at hExec
          simp [EvmYul.Yul.multifill'] at hExec

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_stop
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "stop" [])))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "stop" []
    EvmYul.Operation.STOP (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_stop name expected codeOverride

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_stop
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "stop" [])) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact NativeStmtPreservesWord_exprStmtCall_lowerExprNative_stop name expected _

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log0
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "log0" args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [size, offset])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected args _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected args dispatcher hArgs)
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log1
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "log1" args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [topic0, size, offset])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected args _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected args dispatcher hArgs)
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log2
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "log2" args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [topic1, topic0, size, offset])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected args _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected args dispatcher hArgs)
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log3
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "log3" args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [topic2, topic1, topic0, size, offset])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected args _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected args dispatcher hArgs)
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log4
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "log4" args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2 topic3,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [topic3, topic2, topic1, topic0, size, offset])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected args _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected args dispatcher hArgs)
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log0_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "log0" args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_nativeEvalArgs_preserves
      name expected args _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected args dispatcher hArgs)

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log1_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "log1" args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_nativeEvalArgs_preserves
      name expected args _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected args dispatcher hArgs)

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log2_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "log2" args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_nativeEvalArgs_preserves
      name expected args _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected args dispatcher hArgs)

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log3_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "log3" args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_nativeEvalArgs_preserves
      name expected args _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected args dispatcher hArgs)

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log4_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (args : List YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hArgs :
      ∀ arg, arg ∈ args →
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "log4" args)) = .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_nativeEvalArgs_preserves
      name expected args _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected args dispatcher hArgs)

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_mstore
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (offsetExpr valExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
    (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "mstore" [offsetExpr, valExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel
                (([offsetExpr, valExpr].map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [value, offset])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected [offsetExpr, valExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [offsetExpr, valExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hOffset
          · exact hVal))
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_mstore_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (offsetExpr valExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
    (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "mstore" [offsetExpr, valExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_nativeEvalArgs_preserves
      name expected [offsetExpr, valExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [offsetExpr, valExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hOffset
          · exact hVal))

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_mstore8
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (offsetExpr valExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
    (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "mstore8" [offsetExpr, valExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel
                (([offsetExpr, valExpr].map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [value, offset])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected [offsetExpr, valExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [offsetExpr, valExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hOffset
          · exact hVal))
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_mstore8_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (offsetExpr valExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
    (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "mstore8" [offsetExpr, valExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_nativeEvalArgs_preserves
      name expected [offsetExpr, valExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [offsetExpr, valExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hOffset
          · exact hVal))

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_sstore
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (slotExpr valExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hSlot : Compiler.Proofs.YulGeneration.Backends.BridgedExpr slotExpr)
    (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "sstore" [slotExpr, valExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel
                (([slotExpr, valExpr].map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [value, slot])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected [slotExpr, valExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [slotExpr, valExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hSlot
          · exact hVal))
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_sstore_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (slotExpr valExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hSlot : Compiler.Proofs.YulGeneration.Backends.BridgedExpr slotExpr)
    (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "sstore" [slotExpr, valExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_nativeEvalArgs_preserves
      name expected [slotExpr, valExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [slotExpr, valExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hSlot
          · exact hVal))

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_tstore
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (slotExpr valExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hSlot : Compiler.Proofs.YulGeneration.Backends.BridgedExpr slotExpr)
    (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "tstore" [slotExpr, valExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel
                (([slotExpr, valExpr].map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [value, slot])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected [slotExpr, valExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [slotExpr, valExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hSlot
          · exact hVal))
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_tstore_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (slotExpr valExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hSlot : Compiler.Proofs.YulGeneration.Backends.BridgedExpr slotExpr)
    (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "tstore" [slotExpr, valExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_nativeEvalArgs_preserves
      name expected [slotExpr, valExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [slotExpr, valExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hSlot
          · exact hVal))

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_return
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
    (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "return" [offsetExpr, sizeExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                (([offsetExpr, sizeExpr].map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [size, offset])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected [offsetExpr, sizeExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [offsetExpr, sizeExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hOffset
          · exact hSize))
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_return_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
    (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "return" [offsetExpr, sizeExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_nativeEvalArgs_preserves
      name expected [offsetExpr, sizeExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [offsetExpr, sizeExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hOffset
          · exact hSize))

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_revert
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
    (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "revert" [offsetExpr, sizeExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                (([offsetExpr, sizeExpr].map Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [size, offset])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected [offsetExpr, sizeExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [offsetExpr, sizeExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hOffset
          · exact hSize))
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_revert_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
    (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "revert" [offsetExpr, sizeExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_nativeEvalArgs_preserves
      name expected [offsetExpr, sizeExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [offsetExpr, sizeExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl
          · exact hOffset
          · exact hSize))

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_calldatacopy
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (destOffset sourceOffset sizeExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hDest : Compiler.Proofs.YulGeneration.Backends.BridgedExpr destOffset)
    (hSource : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sourceOffset)
    (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "calldatacopy" [destOffset, sourceOffset, sizeExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart datastart size,
            EvmYul.Yul.evalArgs fuel
                (([destOffset, sourceOffset, sizeExpr].map
                  Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [size, datastart, mstart])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected [destOffset, sourceOffset, sizeExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [destOffset, sourceOffset, sizeExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl | rfl
          · exact hDest
          · exact hSource
          · exact hSize))
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_returndatacopy
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (destOffset sourceOffset sizeExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hDest : Compiler.Proofs.YulGeneration.Backends.BridgedExpr destOffset)
    (hSource : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sourceOffset)
    (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "returndatacopy" [destOffset, sourceOffset, sizeExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hShape :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart rstart size,
            EvmYul.Yul.evalArgs fuel
                (([destOffset, sourceOffset, sizeExpr].map
                  Backends.lowerExprNative).reverse)
                (some
                  { dispatcher := dispatcher
                    functions := ((∅ : NativeFunctionMap).insert
                      "mappingSlot" nativeMappingSlotFunctionDefinition) })
                state =
              .ok (argState, [size, rstart, mstart])) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves
      name expected [destOffset, sourceOffset, sizeExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [destOffset, sourceOffset, sizeExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl | rfl
          · exact hDest
          · exact hSource
          · exact hSize))
      hShape

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_calldatacopy_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (destOffset sourceOffset sizeExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hDest : Compiler.Proofs.YulGeneration.Backends.BridgedExpr destOffset)
    (hSource : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sourceOffset)
    (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "calldatacopy" [destOffset, sourceOffset, sizeExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_nativeEvalArgs_preserves
      name expected [destOffset, sourceOffset, sizeExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [destOffset, sourceOffset, sizeExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl | rfl
          · exact hDest
          · exact hSource
          · exact hSize))

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_returndatacopy_of_nativeEvalArgs
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (destOffset sourceOffset sizeExpr : YulExpr)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hDest : Compiler.Proofs.YulGeneration.Backends.BridgedExpr destOffset)
    (hSource : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sourceOffset)
    (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.exprStmt (.call "returndatacopy" [destOffset, sourceOffset, sizeExpr])) =
          .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
  cases hLower
  simp at hMem
  subst nativeStmt
  exact
    NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_nativeEvalArgs_preserves
      name expected [destOffset, sourceOffset, sizeExpr] _
      (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_bridgedExprs_mappingContract
        name expected [destOffset, sourceOffset, sizeExpr] dispatcher
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with rfl | rfl | rfl
          · exact hDest
          · exact hSource
          · exact hSize))

inductive NativePreservableStraightStmt : YulStmt → Prop
  | comment (text : String) :
      NativePreservableStraightStmt (.comment text)
  | let_ (target : EvmYul.Identifier) (value : YulExpr)
      (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value) :
      NativePreservableStraightStmt (.let_ target value)
  | letMany (targets : List EvmYul.Identifier) (value : YulExpr)
      (hTargets : targets ≠ [])
      (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value) :
      NativePreservableStraightStmt (.letMany targets value)
  | assign (target : EvmYul.Identifier) (value : YulExpr)
      (hValue : Compiler.Proofs.YulGeneration.Backends.BridgedExpr value) :
      NativePreservableStraightStmt (.assign target value)
  | expr_call (func : EvmYul.Identifier) (args : List YulExpr)
      (hName : Compiler.Proofs.YulGeneration.Backends.allowedExprCallName func)
      (hArgs :
        ∀ arg, arg ∈ args →
          Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg) :
      NativePreservableStraightStmt (.exprStmt (.call func args))
  | expr_sstore (slotExpr valExpr : YulExpr)
      (hSlot : Compiler.Proofs.YulGeneration.Backends.BridgedExpr slotExpr)
      (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr) :
      NativePreservableStraightStmt (.exprStmt (.call "sstore" [slotExpr, valExpr]))
  | expr_tstore (slotExpr valExpr : YulExpr)
      (hSlot : Compiler.Proofs.YulGeneration.Backends.BridgedExpr slotExpr)
      (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr) :
      NativePreservableStraightStmt (.exprStmt (.call "tstore" [slotExpr, valExpr]))
  | expr_mstore (offsetExpr valExpr : YulExpr)
      (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
      (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr) :
      NativePreservableStraightStmt (.exprStmt (.call "mstore" [offsetExpr, valExpr]))
  | expr_mstore8 (offsetExpr valExpr : YulExpr)
      (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
      (hVal : Compiler.Proofs.YulGeneration.Backends.BridgedExpr valExpr) :
      NativePreservableStraightStmt (.exprStmt (.call "mstore8" [offsetExpr, valExpr]))
  | expr_stop :
      NativePreservableStraightStmt (.exprStmt (.call "stop" []))
  | expr_return (offsetExpr sizeExpr : YulExpr)
      (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
      (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr) :
      NativePreservableStraightStmt
        (.exprStmt (.call "return" [offsetExpr, sizeExpr]))
  | expr_revert (offsetExpr sizeExpr : YulExpr)
      (hOffset : Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr)
      (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr) :
      NativePreservableStraightStmt
        (.exprStmt (.call "revert" [offsetExpr, sizeExpr]))
  | expr_log0 (args : List YulExpr)
      (hArgs :
        ∀ arg, arg ∈ args →
          Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg) :
      NativePreservableStraightStmt (.exprStmt (.call "log0" args))
  | expr_log1 (args : List YulExpr)
      (hArgs :
        ∀ arg, arg ∈ args →
          Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg) :
      NativePreservableStraightStmt (.exprStmt (.call "log1" args))
  | expr_log2 (args : List YulExpr)
      (hArgs :
        ∀ arg, arg ∈ args →
          Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg) :
      NativePreservableStraightStmt (.exprStmt (.call "log2" args))
  | expr_log3 (args : List YulExpr)
      (hArgs :
        ∀ arg, arg ∈ args →
          Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg) :
      NativePreservableStraightStmt (.exprStmt (.call "log3" args))
  | expr_log4 (args : List YulExpr)
      (hArgs :
        ∀ arg, arg ∈ args →
          Compiler.Proofs.YulGeneration.Backends.BridgedExpr arg) :
      NativePreservableStraightStmt (.exprStmt (.call "log4" args))
  | expr_calldatacopy (destOffset sourceOffset sizeExpr : YulExpr)
      (hDest : Compiler.Proofs.YulGeneration.Backends.BridgedExpr destOffset)
      (hSource : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sourceOffset)
      (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr) :
      NativePreservableStraightStmt
        (.exprStmt (.call "calldatacopy" [destOffset, sourceOffset, sizeExpr]))
  | expr_returndatacopy (destOffset sourceOffset sizeExpr : YulExpr)
      (hDest : Compiler.Proofs.YulGeneration.Backends.BridgedExpr destOffset)
      (hSource : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sourceOffset)
      (hSize : Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr) :
      NativePreservableStraightStmt
        (.exprStmt (.call "returndatacopy" [destOffset, sourceOffset, sizeExpr]))

/-- Mapping-free straight statements whose lowered native form preserves a
marker word for the actual runtime contract.

This is intentionally parallel to `NativePreservableStraightStmt`, but every
expression premise is recursive `NativeMappingFreeBridgedExpr`. The mapping
helper path remains covered by `NativePreservableStraightStmt`; this fragment is
for no-mapping/generated bodies that should not require the synthetic
`mappingSlot` contract. -/
inductive NativeMappingFreePreservableStraightStmt : YulStmt → Prop
  | comment (text : String) :
      NativeMappingFreePreservableStraightStmt (.comment text)
  | let_ (target : EvmYul.Identifier) (value : YulExpr)
      (hValue : NativeMappingFreeBridgedExpr value) :
      NativeMappingFreePreservableStraightStmt (.let_ target value)
  | letMany (targets : List EvmYul.Identifier) (value : YulExpr)
      (hTargets : targets ≠ [])
      (hValue : NativeMappingFreeBridgedExpr value) :
      NativeMappingFreePreservableStraightStmt (.letMany targets value)
  | assign (target : EvmYul.Identifier) (value : YulExpr)
      (hValue : NativeMappingFreeBridgedExpr value) :
      NativeMappingFreePreservableStraightStmt (.assign target value)
  | expr_call (func : EvmYul.Identifier) (args : List YulExpr)
      (hName : Compiler.Proofs.YulGeneration.Backends.allowedExprCallName func)
      (hNoMapping : func ≠ "mappingSlot")
      (hArgs : ∀ arg, arg ∈ args → NativeMappingFreeBridgedExpr arg) :
      NativeMappingFreePreservableStraightStmt (.exprStmt (.call func args))
  | expr_sstore (slotExpr valExpr : YulExpr)
      (hSlot : NativeMappingFreeBridgedExpr slotExpr)
      (hVal : NativeMappingFreeBridgedExpr valExpr) :
      NativeMappingFreePreservableStraightStmt
        (.exprStmt (.call "sstore" [slotExpr, valExpr]))
  | expr_tstore (slotExpr valExpr : YulExpr)
      (hSlot : NativeMappingFreeBridgedExpr slotExpr)
      (hVal : NativeMappingFreeBridgedExpr valExpr) :
      NativeMappingFreePreservableStraightStmt
        (.exprStmt (.call "tstore" [slotExpr, valExpr]))
  | expr_mstore (offsetExpr valExpr : YulExpr)
      (hOffset : NativeMappingFreeBridgedExpr offsetExpr)
      (hVal : NativeMappingFreeBridgedExpr valExpr) :
      NativeMappingFreePreservableStraightStmt
        (.exprStmt (.call "mstore" [offsetExpr, valExpr]))
  | expr_mstore8 (offsetExpr valExpr : YulExpr)
      (hOffset : NativeMappingFreeBridgedExpr offsetExpr)
      (hVal : NativeMappingFreeBridgedExpr valExpr) :
      NativeMappingFreePreservableStraightStmt
        (.exprStmt (.call "mstore8" [offsetExpr, valExpr]))
  | expr_stop :
      NativeMappingFreePreservableStraightStmt (.exprStmt (.call "stop" []))
  | expr_return (offsetExpr sizeExpr : YulExpr)
      (hOffset : NativeMappingFreeBridgedExpr offsetExpr)
      (hSize : NativeMappingFreeBridgedExpr sizeExpr) :
      NativeMappingFreePreservableStraightStmt
        (.exprStmt (.call "return" [offsetExpr, sizeExpr]))
  | expr_revert (offsetExpr sizeExpr : YulExpr)
      (hOffset : NativeMappingFreeBridgedExpr offsetExpr)
      (hSize : NativeMappingFreeBridgedExpr sizeExpr) :
      NativeMappingFreePreservableStraightStmt
        (.exprStmt (.call "revert" [offsetExpr, sizeExpr]))
  | expr_log0 (args : List YulExpr)
      (hArgs : ∀ arg, arg ∈ args → NativeMappingFreeBridgedExpr arg) :
      NativeMappingFreePreservableStraightStmt (.exprStmt (.call "log0" args))
  | expr_log1 (args : List YulExpr)
      (hArgs : ∀ arg, arg ∈ args → NativeMappingFreeBridgedExpr arg) :
      NativeMappingFreePreservableStraightStmt (.exprStmt (.call "log1" args))
  | expr_log2 (args : List YulExpr)
      (hArgs : ∀ arg, arg ∈ args → NativeMappingFreeBridgedExpr arg) :
      NativeMappingFreePreservableStraightStmt (.exprStmt (.call "log2" args))
  | expr_log3 (args : List YulExpr)
      (hArgs : ∀ arg, arg ∈ args → NativeMappingFreeBridgedExpr arg) :
      NativeMappingFreePreservableStraightStmt (.exprStmt (.call "log3" args))
  | expr_log4 (args : List YulExpr)
      (hArgs : ∀ arg, arg ∈ args → NativeMappingFreeBridgedExpr arg) :
      NativeMappingFreePreservableStraightStmt (.exprStmt (.call "log4" args))
  | expr_calldatacopy (destOffset sourceOffset sizeExpr : YulExpr)
      (hDest : NativeMappingFreeBridgedExpr destOffset)
      (hSource : NativeMappingFreeBridgedExpr sourceOffset)
      (hSize : NativeMappingFreeBridgedExpr sizeExpr) :
      NativeMappingFreePreservableStraightStmt
        (.exprStmt (.call "calldatacopy" [destOffset, sourceOffset, sizeExpr]))
  | expr_returndatacopy (destOffset sourceOffset sizeExpr : YulExpr)
      (hDest : NativeMappingFreeBridgedExpr destOffset)
      (hSource : NativeMappingFreeBridgedExpr sourceOffset)
      (hSize : NativeMappingFreeBridgedExpr sizeExpr) :
      NativeMappingFreePreservableStraightStmt
        (.exprStmt (.call "returndatacopy" [destOffset, sourceOffset, sizeExpr]))

def NativeMappingFreePreservableStraightStmts (stmts : List YulStmt) : Prop :=
  ∀ stmt, stmt ∈ stmts → NativeMappingFreePreservableStraightStmt stmt

/-- Extra facts needed to translate a historical `BridgedExpr` witness into
the mapping-free native fragment. The historical predicate admits the
`mappingSlot` helper; the actual-runtime preservation path excludes it
recursively. -/
def NativeMappingFreeSideConditionForBridgedExpr : YulExpr → Prop
  | .call "mappingSlot" _ => False
  | .call _ args =>
      ∀ arg, arg ∈ args → NativeMappingFreeSideConditionForBridgedExpr arg
  | _ => True

theorem NativeMappingFreeBridgedExpr.of_bridgedExpr
    {expr : YulExpr}
    (hExpr : Compiler.Proofs.YulGeneration.Backends.BridgedExpr expr)
    (hSide : NativeMappingFreeSideConditionForBridgedExpr expr) :
    NativeMappingFreeBridgedExpr expr := by
  induction hExpr with
  | lit n =>
      exact NativeMappingFreeBridgedExpr.lit n
  | hex n =>
      exact NativeMappingFreeBridgedExpr.hex n
  | str s =>
      exact NativeMappingFreeBridgedExpr.str s
  | ident name =>
      exact NativeMappingFreeBridgedExpr.ident name
  | call func args hName hArgs ih =>
      have hNoMapping : func ≠ "mappingSlot" := by
        intro hFunc
        subst func
        simp [NativeMappingFreeSideConditionForBridgedExpr] at hSide
      have hArgsSide :
          ∀ arg, arg ∈ args →
            NativeMappingFreeSideConditionForBridgedExpr arg := by
        simpa [NativeMappingFreeSideConditionForBridgedExpr, hNoMapping] using
          hSide
      exact
        NativeMappingFreeBridgedExpr.call func args hName hNoMapping
          (by
            intro arg hArg
            exact ih arg hArg (hArgsSide arg hArg))

/-- Extra facts needed to view a historical `BridgedStraightStmt` as a
mapping-free native matched-flag-preservable straight statement.

The side condition excludes the mapping helper and other non-straight
function-body forms while making the few historical gaps explicit (`letMany`
values and `revert` arguments). -/
def NativeMappingFreeSideConditionForBridgedStraightStmt :
    YulStmt → Prop
  | .let_ _ value =>
      NativeMappingFreeSideConditionForBridgedExpr value
  | .letMany targets value =>
      targets ≠ [] ∧ NativeMappingFreeBridgedExpr value
  | .assign _ value =>
      NativeMappingFreeSideConditionForBridgedExpr value
  | .exprStmt (.call "sstore" [.call "mappingSlot" _, _]) => False
  | .exprStmt (.call "sstore" [.lit _, valExpr]) =>
      NativeMappingFreeSideConditionForBridgedExpr valExpr
  | .exprStmt (.call "sstore" [.ident _, valExpr]) =>
      NativeMappingFreeSideConditionForBridgedExpr valExpr
  | .exprStmt (.call "sstore" [.call "add" [leftExpr, rightExpr], valExpr]) =>
      NativeMappingFreeSideConditionForBridgedExpr leftExpr ∧
        NativeMappingFreeSideConditionForBridgedExpr rightExpr ∧
        NativeMappingFreeSideConditionForBridgedExpr valExpr
  | .exprStmt (.call "mstore" [offsetExpr, valExpr]) =>
      NativeMappingFreeSideConditionForBridgedExpr offsetExpr ∧
        NativeMappingFreeSideConditionForBridgedExpr valExpr
  | .exprStmt (.call "tstore" [offsetExpr, valExpr]) =>
      NativeMappingFreeSideConditionForBridgedExpr offsetExpr ∧
        NativeMappingFreeSideConditionForBridgedExpr valExpr
  | .exprStmt (.call "return" [offsetExpr, sizeExpr]) =>
      NativeMappingFreeSideConditionForBridgedExpr offsetExpr ∧
        NativeMappingFreeSideConditionForBridgedExpr sizeExpr
  | .exprStmt (.call "revert" [offsetExpr, sizeExpr]) =>
      NativeMappingFreeBridgedExpr offsetExpr ∧
        NativeMappingFreeBridgedExpr sizeExpr
  | .exprStmt (.call func args) =>
      Compiler.Proofs.YulGeneration.isYulLogName func = true →
        ∀ arg, arg ∈ args → NativeMappingFreeSideConditionForBridgedExpr arg
  | .«leave» => False
  | .funcDef _ _ _ _ => False
  | _ => True

/-- Translate the older straight bridged predicate into the no-mapping native
matched-flag-preservation fragment.

This lets generated no-mapping bodies reuse `BridgedStraightStmts` closure
proofs while still targeting the actual lowered runtime contract rather than a
synthetic mapping-helper contract. -/
theorem NativeMappingFreePreservableStraightStmt.of_bridgedStraightStmt
    {stmt : YulStmt}
    (hStmt :
      Compiler.Proofs.YulGeneration.Backends.BridgedStraightStmt stmt)
    (hSide :
      NativeMappingFreeSideConditionForBridgedStraightStmt stmt) :
    NativeMappingFreePreservableStraightStmt stmt := by
  cases hStmt with
  | comment text =>
      exact NativeMappingFreePreservableStraightStmt.comment text
  | let_ name value hValue =>
      exact
        NativeMappingFreePreservableStraightStmt.let_ name value
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hValue hSide)
  | letMany names value =>
      exact
        NativeMappingFreePreservableStraightStmt.letMany names value
          hSide.1 hSide.2
  | assign name value hValue =>
      exact
        NativeMappingFreePreservableStraightStmt.assign name value
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hValue hSide)
  | «leave» =>
      cases hSide
  | expr_sstore_mapping baseExpr keyExpr valExpr hBase hKey hVal =>
      cases hSide
  | expr_sstore_lit slot valExpr hVal =>
      exact
        NativeMappingFreePreservableStraightStmt.expr_sstore (.lit slot) valExpr
          (NativeMappingFreeBridgedExpr.lit slot)
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hVal hSide)
  | expr_sstore_ident slotName valExpr hVal =>
      exact
        NativeMappingFreePreservableStraightStmt.expr_sstore (.ident slotName)
          valExpr (NativeMappingFreeBridgedExpr.ident slotName)
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hVal hSide)
  | expr_sstore_add leftExpr rightExpr valExpr hLeft hRight hVal =>
      exact
        NativeMappingFreePreservableStraightStmt.expr_sstore
          (.call "add" [leftExpr, rightExpr]) valExpr
          (NativeMappingFreeBridgedExpr.call "add" [leftExpr, rightExpr]
            (by
              left
              simp [Compiler.Proofs.YulGeneration.Backends.bridgedBuiltins])
            (by decide)
            (by
              intro arg hArg
              simp at hArg
              rcases hArg with rfl | rfl
              · exact
                  NativeMappingFreeBridgedExpr.of_bridgedExpr hLeft hSide.1
              · exact
                  NativeMappingFreeBridgedExpr.of_bridgedExpr hRight hSide.2.1))
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hVal hSide.2.2)
  | expr_mstore offsetExpr valExpr hOffset hVal =>
      exact
        NativeMappingFreePreservableStraightStmt.expr_mstore offsetExpr valExpr
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hOffset hSide.1)
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hVal hSide.2)
  | expr_tstore offsetExpr valExpr hOffset hVal =>
      exact
        NativeMappingFreePreservableStraightStmt.expr_tstore offsetExpr valExpr
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hOffset hSide.1)
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hVal hSide.2)
  | expr_stop =>
      exact NativeMappingFreePreservableStraightStmt.expr_stop
  | expr_return offsetExpr sizeExpr hOffset hSize =>
      exact
        NativeMappingFreePreservableStraightStmt.expr_return offsetExpr sizeExpr
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hOffset hSide.1)
          (NativeMappingFreeBridgedExpr.of_bridgedExpr hSize hSide.2)
  | expr_revert offsetExpr sizeExpr =>
      exact
        NativeMappingFreePreservableStraightStmt.expr_revert offsetExpr sizeExpr
          hSide.1 hSide.2
  | expr_log func args hLog hArgs =>
      have hFunc :
          func = "log0" ∨ func = "log1" ∨ func = "log2" ∨
            func = "log3" ∨ func = "log4" := by
        simp [Compiler.Proofs.YulGeneration.isYulLogName] at hLog
        tauto
      rcases hFunc with rfl | rfl | rfl | rfl | rfl
      · refine NativeMappingFreePreservableStraightStmt.expr_log0 args ?_
        have hArgsSide :
            ∀ arg, arg ∈ args →
              NativeMappingFreeSideConditionForBridgedExpr arg := by
          simpa [NativeMappingFreeSideConditionForBridgedStraightStmt] using
            (hSide (by simp [Compiler.Proofs.YulGeneration.isYulLogName]))
        intro arg hArg
        exact
          NativeMappingFreeBridgedExpr.of_bridgedExpr (hArgs arg hArg)
            (hArgsSide arg hArg)
      · refine NativeMappingFreePreservableStraightStmt.expr_log1 args ?_
        have hArgsSide :
            ∀ arg, arg ∈ args →
              NativeMappingFreeSideConditionForBridgedExpr arg := by
          simpa [NativeMappingFreeSideConditionForBridgedStraightStmt] using
            (hSide (by simp [Compiler.Proofs.YulGeneration.isYulLogName]))
        intro arg hArg
        exact
          NativeMappingFreeBridgedExpr.of_bridgedExpr (hArgs arg hArg)
            (hArgsSide arg hArg)
      · refine NativeMappingFreePreservableStraightStmt.expr_log2 args ?_
        have hArgsSide :
            ∀ arg, arg ∈ args →
              NativeMappingFreeSideConditionForBridgedExpr arg := by
          simpa [NativeMappingFreeSideConditionForBridgedStraightStmt] using
            (hSide (by simp [Compiler.Proofs.YulGeneration.isYulLogName]))
        intro arg hArg
        exact
          NativeMappingFreeBridgedExpr.of_bridgedExpr (hArgs arg hArg)
            (hArgsSide arg hArg)
      · refine NativeMappingFreePreservableStraightStmt.expr_log3 args ?_
        have hArgsSide :
            ∀ arg, arg ∈ args →
              NativeMappingFreeSideConditionForBridgedExpr arg := by
          simpa [NativeMappingFreeSideConditionForBridgedStraightStmt] using
            (hSide (by simp [Compiler.Proofs.YulGeneration.isYulLogName]))
        intro arg hArg
        exact
          NativeMappingFreeBridgedExpr.of_bridgedExpr (hArgs arg hArg)
            (hArgsSide arg hArg)
      · refine NativeMappingFreePreservableStraightStmt.expr_log4 args ?_
        have hArgsSide :
            ∀ arg, arg ∈ args →
              NativeMappingFreeSideConditionForBridgedExpr arg := by
          simpa [NativeMappingFreeSideConditionForBridgedStraightStmt] using
            (hSide (by simp [Compiler.Proofs.YulGeneration.isYulLogName]))
        intro arg hArg
        exact
          NativeMappingFreeBridgedExpr.of_bridgedExpr (hArgs arg hArg)
            (hArgsSide arg hArg)
  | funcDef name params rets body =>
      cases hSide

theorem NativeMappingFreePreservableStraightStmts.of_bridgedStraightStmts
    {stmts : List YulStmt}
    (hStmts :
      Compiler.Proofs.YulGeneration.Backends.BridgedStraightStmts stmts)
    (hSide :
      ∀ stmt, stmt ∈ stmts →
        NativeMappingFreeSideConditionForBridgedStraightStmt stmt) :
    NativeMappingFreePreservableStraightStmts stmts := by
  intro stmt hMem
  exact
    NativeMappingFreePreservableStraightStmt.of_bridgedStraightStmt
      (hStmts stmt hMem) (hSide stmt hMem)

/-- Extra facts needed to view a historical `BridgedStraightStmt` as a native
matched-flag-preservable straight statement.

Most bridged-straight constructors already carry exactly the data needed by
`NativePreservableStraightStmt`. The exceptions are explicit here: `letMany`
needs a nonempty target list and a bridged value, `revert` needs bridged
arguments, and `leave`/`funcDef` are outside this native preservation fragment.
-/
def NativePreservableSideConditionForBridgedStraightStmt :
    YulStmt → Prop
  | .letMany targets value =>
      targets ≠ [] ∧
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr value
  | .exprStmt (.call "revert" [offsetExpr, sizeExpr]) =>
      Compiler.Proofs.YulGeneration.Backends.BridgedExpr offsetExpr ∧
        Compiler.Proofs.YulGeneration.Backends.BridgedExpr sizeExpr
  | .«leave» => False
  | .funcDef _ _ _ _ => False
  | _ => True

private theorem bridgedExpr_mappingSlot_of_bridged
    (baseExpr keyExpr : YulExpr)
    (hBase : Compiler.Proofs.YulGeneration.Backends.BridgedExpr baseExpr)
    (hKey : Compiler.Proofs.YulGeneration.Backends.BridgedExpr keyExpr) :
    Compiler.Proofs.YulGeneration.Backends.BridgedExpr
      (.call "mappingSlot" [baseExpr, keyExpr]) := by
  exact
    Compiler.Proofs.YulGeneration.Backends.BridgedExpr.call "mappingSlot"
      [baseExpr, keyExpr]
      (by
        left
        simp [Compiler.Proofs.YulGeneration.Backends.bridgedBuiltins])
      (by
        intro arg hArg
        simp at hArg
        rcases hArg with rfl | rfl
        · exact hBase
        · exact hKey)

/-- Translate the older straight bridged predicate into the native
matched-flag-preservation fragment, making the few missing side conditions
explicit.

This is a reusable bridge for selector-hit success: once generated bodies are
shown to compile into the straight bridged fragment with these side conditions,
the native harness can derive per-statement matched-flag preservation without
the dispatcher proof carrying an ad hoc predicate conversion. -/
theorem NativePreservableStraightStmt.of_bridgedStraightStmt
    {stmt : YulStmt}
    (hStmt :
      Compiler.Proofs.YulGeneration.Backends.BridgedStraightStmt stmt)
    (hSide :
      NativePreservableSideConditionForBridgedStraightStmt stmt) :
    NativePreservableStraightStmt stmt := by
  cases hStmt with
  | comment text =>
      exact NativePreservableStraightStmt.comment text
  | let_ name value hValue =>
      exact NativePreservableStraightStmt.let_ name value hValue
  | letMany names value =>
      exact NativePreservableStraightStmt.letMany names value hSide.1 hSide.2
  | assign name value hValue =>
      exact NativePreservableStraightStmt.assign name value hValue
  | «leave» =>
      cases hSide
  | expr_sstore_mapping baseExpr keyExpr valExpr hBase hKey hVal =>
      exact
        NativePreservableStraightStmt.expr_sstore
          (.call "mappingSlot" [baseExpr, keyExpr]) valExpr
          (bridgedExpr_mappingSlot_of_bridged baseExpr keyExpr hBase hKey)
          hVal
  | expr_sstore_lit slot valExpr hVal =>
      exact
        NativePreservableStraightStmt.expr_sstore (.lit slot) valExpr
          (Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit slot) hVal
  | expr_sstore_ident slotName valExpr hVal =>
      exact
        NativePreservableStraightStmt.expr_sstore (.ident slotName) valExpr
          (Compiler.Proofs.YulGeneration.Backends.BridgedExpr.ident slotName)
          hVal
  | expr_sstore_add leftExpr rightExpr valExpr hLeft hRight hVal =>
      exact
        NativePreservableStraightStmt.expr_sstore
          (.call "add" [leftExpr, rightExpr]) valExpr
          (Compiler.Proofs.YulGeneration.Backends.BridgedExpr.call "add"
            [leftExpr, rightExpr]
            (by
              left
              simp [Compiler.Proofs.YulGeneration.Backends.bridgedBuiltins])
            (by
              intro arg hArg
              simp at hArg
              rcases hArg with rfl | rfl
              · exact hLeft
              · exact hRight))
          hVal
  | expr_mstore offsetExpr valExpr hOffset hVal =>
      exact NativePreservableStraightStmt.expr_mstore offsetExpr valExpr hOffset hVal
  | expr_tstore offsetExpr valExpr hOffset hVal =>
      exact NativePreservableStraightStmt.expr_tstore offsetExpr valExpr hOffset hVal
  | expr_stop =>
      exact NativePreservableStraightStmt.expr_stop
  | expr_return offsetExpr sizeExpr hOffset hSize =>
      exact NativePreservableStraightStmt.expr_return offsetExpr sizeExpr hOffset hSize
  | expr_revert offsetExpr sizeExpr =>
      exact NativePreservableStraightStmt.expr_revert offsetExpr sizeExpr hSide.1 hSide.2
  | expr_log func args hLog hArgs =>
      have hFunc :
          func = "log0" ∨ func = "log1" ∨ func = "log2" ∨
            func = "log3" ∨ func = "log4" := by
        simp [Compiler.Proofs.YulGeneration.isYulLogName] at hLog
        tauto
      rcases hFunc with rfl | rfl | rfl | rfl | rfl
      · exact NativePreservableStraightStmt.expr_log0 args hArgs
      · exact NativePreservableStraightStmt.expr_log1 args hArgs
      · exact NativePreservableStraightStmt.expr_log2 args hArgs
      · exact NativePreservableStraightStmt.expr_log3 args hArgs
      · exact NativePreservableStraightStmt.expr_log4 args hArgs
  | funcDef name params rets body =>
      cases hSide

def NativePreservableStraightStmts (stmts : List YulStmt) : Prop :=
  ∀ stmt, stmt ∈ stmts → NativePreservableStraightStmt stmt

theorem NativePreservableStraightStmts.of_bridgedStraightStmts
    {stmts : List YulStmt}
    (hStmts :
      Compiler.Proofs.YulGeneration.Backends.BridgedStraightStmts stmts)
    (hSide :
      ∀ stmt, stmt ∈ stmts →
        NativePreservableSideConditionForBridgedStraightStmt stmt) :
    NativePreservableStraightStmts stmts := by
  intro stmt hMem
  exact
    NativePreservableStraightStmt.of_bridgedStraightStmt
      (hStmts stmt hMem) (hSide stmt hMem)

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_of_mappingFreePreservableStraightStmt
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (stmt : YulStmt)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hStmt : NativeMappingFreePreservableStraightStmt stmt)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId stmt =
        .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hFresh : (name : String) ∉ Backends.nativeStmtWriteNames nativeStmt) :
    NativeStmtPreservesWord name expected nativeStmt codeOverride := by
  induction hStmt with
  | comment text =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_comment] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact NativeStmtPreservesWord_empty_block name expected codeOverride
  | let_ target value hValue =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_let] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_let_lowerExprNative_of_mappingFreeBridgedExpr
          name expected target value codeOverride
          (nativeStmtWriteNames_let_singleton_not_mem_ne name target
            (some (Backends.lowerExprNative value)) hFresh)
          hValue
  | letMany targets value hTargets hValue =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_letMany] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_letMany_lowerExprNative_of_mappingFreeBridgedExpr
          name expected targets value codeOverride hTargets
          (nativeStmtWriteNames_let_not_mem_vars name targets
            (some (Backends.lowerExprNative value)) hFresh)
          hValue
  | assign target value hValue =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_assign] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_lowerAssignNative_of_mappingFreeBridgedExpr
          name expected target value codeOverride
          (nativeStmtWriteNames_lowerAssignNative_not_mem_ne name target value
            hFresh)
          hValue
  | expr_call func args hName hNoMapping hArgs =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      have hNativeArgs :
          NativeEvalArgsPreservesWord name expected
            ((args.map Backends.lowerExprNative).reverse) codeOverride :=
        NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
          name expected args codeOverride hArgs
      cases hOp : Backends.lookupRuntimePrimOp func with
      | some op =>
          exact
            NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
              name func expected args op codeOverride hOp hNativeArgs
              (NativePrimCallPreservesWord_of_allowed_lookupRuntimePrimOp
                name func expected op hName hOp)
      | none =>
          exfalso
          exact lookupRuntimePrimOp_ne_none_of_allowed_of_ne_mappingSlot
            func hName hNoMapping hOp
  | expr_sstore slotExpr valExpr hSlot hVal =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_nativeEvalArgs_preserves
          name expected [slotExpr, valExpr] codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected [slotExpr, valExpr] codeOverride
            (by
              intro arg hArg
              simp at hArg
              rcases hArg with rfl | rfl
              · exact hSlot
              · exact hVal))
  | expr_tstore slotExpr valExpr hSlot hVal =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_nativeEvalArgs_preserves
          name expected [slotExpr, valExpr] codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected [slotExpr, valExpr] codeOverride
            (by
              intro arg hArg
              simp at hArg
              rcases hArg with rfl | rfl
              · exact hSlot
              · exact hVal))
  | expr_mstore offsetExpr valExpr hOffset hVal =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_nativeEvalArgs_preserves
          name expected [offsetExpr, valExpr] codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected [offsetExpr, valExpr] codeOverride
            (by
              intro arg hArg
              simp at hArg
              rcases hArg with rfl | rfl
              · exact hOffset
              · exact hVal))
  | expr_mstore8 offsetExpr valExpr hOffset hVal =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_nativeEvalArgs_preserves
          name expected [offsetExpr, valExpr] codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected [offsetExpr, valExpr] codeOverride
            (by
              intro arg hArg
              simp at hArg
              rcases hArg with rfl | rfl
              · exact hOffset
              · exact hVal))
  | expr_stop =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact NativeStmtPreservesWord_exprStmtCall_lowerExprNative_stop
        name expected codeOverride
  | expr_return offsetExpr sizeExpr hOffset hSize =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_nativeEvalArgs_preserves
          name expected [offsetExpr, sizeExpr] codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected [offsetExpr, sizeExpr] codeOverride
            (by
              intro arg hArg
              simp at hArg
              rcases hArg with rfl | rfl
              · exact hOffset
              · exact hSize))
  | expr_revert offsetExpr sizeExpr hOffset hSize =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_nativeEvalArgs_preserves
          name expected [offsetExpr, sizeExpr] codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected [offsetExpr, sizeExpr] codeOverride
            (by
              intro arg hArg
              simp at hArg
              rcases hArg with rfl | rfl
              · exact hOffset
              · exact hSize))
  | expr_log0 args hArgs =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_nativeEvalArgs_preserves
          name expected args codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected args codeOverride hArgs)
  | expr_log1 args hArgs =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_nativeEvalArgs_preserves
          name expected args codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected args codeOverride hArgs)
  | expr_log2 args hArgs =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_nativeEvalArgs_preserves
          name expected args codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected args codeOverride hArgs)
  | expr_log3 args hArgs =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_nativeEvalArgs_preserves
          name expected args codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected args codeOverride hArgs)
  | expr_log4 args hArgs =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_nativeEvalArgs_preserves
          name expected args codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected args codeOverride hArgs)
  | expr_calldatacopy destOffset sourceOffset sizeExpr hDest hSource hSize =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_nativeEvalArgs_preserves
          name expected [destOffset, sourceOffset, sizeExpr] codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected [destOffset, sourceOffset, sizeExpr] codeOverride
            (by
              intro arg hArg
              simp at hArg
              rcases hArg with rfl | rfl | rfl
              · exact hDest
              · exact hSource
              · exact hSize))
  | expr_returndatacopy destOffset sourceOffset sizeExpr hDest hSource hSize =>
      rw [Backends.lowerStmtGroupNativeWithSwitchIds_expr] at hLower
      cases hLower
      simp at hMem
      subst nativeStmt
      exact
        NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_nativeEvalArgs_preserves
          name expected [destOffset, sourceOffset, sizeExpr] codeOverride
          (NativeEvalArgsPreservesWord_lowerExprNative_reverse_of_mappingFreeBridgedExprs
            name expected [destOffset, sourceOffset, sizeExpr] codeOverride
            (by
              intro arg hArg
              simp at hArg
              rcases hArg with rfl | rfl | rfl
              · exact hDest
              · exact hSource
              · exact hSize))

theorem NativeStmtPreservesWord_of_mem_lowerStmtsNativeWithSwitchIds_of_mappingFreePreservableStraightStmts
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (stmts : List YulStmt)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hStmts : NativeMappingFreePreservableStraightStmts stmts)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts =
        .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hFresh : (name : String) ∉ Backends.nativeStmtWriteNames nativeStmt) :
    NativeStmtPreservesWord name expected nativeStmt codeOverride := by
  induction stmts generalizing nextSwitchId native finalSwitchId with
  | nil =>
      rw [Backends.lowerStmtsNativeWithSwitchIds_nil] at hLower
      cases hLower
      simp at hMem
  | cons stmt rest ih =>
      rw [Backends.lowerStmtsNativeWithSwitchIds_cons] at hLower
      cases hHeadLower :
          Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId stmt with
      | error err =>
          rw [hHeadLower] at hLower
          simp only [Bind.bind, Except.bind, reduceCtorEq] at hLower
      | ok headPair =>
          rcases headPair with ⟨headNative, midSwitchId⟩
          rw [hHeadLower] at hLower
          simp only [Bind.bind, Except.bind] at hLower
          cases hRestLower :
              Backends.lowerStmtsNativeWithSwitchIds reservedNames midSwitchId rest with
          | error err =>
              rw [hRestLower] at hLower
              simp only [reduceCtorEq] at hLower
          | ok restPair =>
              rcases restPair with ⟨restNative, restSwitchId⟩
              rw [hRestLower] at hLower
              simp only [Pure.pure, Except.pure, Except.ok.injEq,
                Prod.mk.injEq] at hLower
              obtain ⟨hNative, hFinal⟩ := hLower
              subst hNative
              subst hFinal
              rw [List.mem_append] at hMem
              rcases hMem with hMem | hMem
              · exact
                  NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_of_mappingFreePreservableStraightStmt
                    name expected reservedNames nextSwitchId stmt headNative
                    midSwitchId nativeStmt codeOverride
                    (hStmts stmt (by simp)) hHeadLower hMem hFresh
              · exact
                  ih midSwitchId restNative restSwitchId
                    (by
                      intro restStmt hRestMem
                      exact hStmts restStmt (by simp [hRestMem]))
                    hRestLower hMem

theorem NativeBlockPreservesWord_lowerStmtsNativeWithSwitchIds_of_mappingFreePreservableStraightStmts
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (stmts : List YulStmt)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hStmts : NativeMappingFreePreservableStraightStmts stmts)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts =
        .ok (native, finalSwitchId))
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames native) :
    NativeBlockPreservesWord name expected native codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem name expected native
    codeOverride hFresh
    (by
      intro nativeStmt hMem hStmtFresh
      exact
        NativeStmtPreservesWord_of_mem_lowerStmtsNativeWithSwitchIds_of_mappingFreePreservableStraightStmts
          name expected reservedNames nextSwitchId stmts native finalSwitchId
          nativeStmt codeOverride hStmts hLower hMem hStmtFresh)

theorem NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_of_nativePreservableStraightStmt
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (stmt : YulStmt)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hStmt : NativePreservableStraightStmt stmt)
    (hLower :
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId stmt =
        .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hFresh : (name : String) ∉ Backends.nativeStmtWriteNames nativeStmt) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  induction hStmt with
  | comment text =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_comment
          name expected reservedNames nextSwitchId text native finalSwitchId
          dispatcher nativeStmt hLower hMem
  | let_ target value hValue =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_let_of_write_not_mem
          name expected reservedNames nextSwitchId target value native finalSwitchId
          dispatcher nativeStmt hValue hLower hMem hFresh
  | letMany targets value hTargets hValue =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_letMany_of_write_not_mem
          name expected reservedNames nextSwitchId targets value native finalSwitchId
          dispatcher nativeStmt hTargets hValue hLower hMem hFresh
  | assign target value hValue =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_assign_of_write_not_mem
          name expected reservedNames nextSwitchId target value native finalSwitchId
          dispatcher nativeStmt hValue hLower hMem hFresh
  | expr_call func args hName hArgs =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_call_of_bridgedExpr_mappingContract
          name expected reservedNames nextSwitchId func args native finalSwitchId
          dispatcher nativeStmt hName hArgs hLower hMem
  | expr_sstore slotExpr valExpr hSlot hVal =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_sstore_of_nativeEvalArgs
          name expected reservedNames nextSwitchId slotExpr valExpr native
          finalSwitchId dispatcher nativeStmt hSlot hVal hLower hMem
  | expr_tstore slotExpr valExpr hSlot hVal =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_tstore_of_nativeEvalArgs
          name expected reservedNames nextSwitchId slotExpr valExpr native
          finalSwitchId dispatcher nativeStmt hSlot hVal hLower hMem
  | expr_mstore offsetExpr valExpr hOffset hVal =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_mstore_of_nativeEvalArgs
          name expected reservedNames nextSwitchId offsetExpr valExpr native
          finalSwitchId dispatcher nativeStmt hOffset hVal hLower hMem
  | expr_mstore8 offsetExpr valExpr hOffset hVal =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_mstore8_of_nativeEvalArgs
          name expected reservedNames nextSwitchId offsetExpr valExpr native
          finalSwitchId dispatcher nativeStmt hOffset hVal hLower hMem
  | expr_stop =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_stop
          name expected reservedNames nextSwitchId native finalSwitchId
          dispatcher nativeStmt hLower hMem
  | expr_return offsetExpr sizeExpr hOffset hSize =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_return_of_nativeEvalArgs
          name expected reservedNames nextSwitchId offsetExpr sizeExpr native
          finalSwitchId dispatcher nativeStmt hOffset hSize hLower hMem
  | expr_revert offsetExpr sizeExpr hOffset hSize =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_revert_of_nativeEvalArgs
          name expected reservedNames nextSwitchId offsetExpr sizeExpr native
          finalSwitchId dispatcher nativeStmt hOffset hSize hLower hMem
  | expr_log0 args hArgs =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log0_of_nativeEvalArgs
          name expected reservedNames nextSwitchId args native finalSwitchId
          dispatcher nativeStmt hArgs hLower hMem
  | expr_log1 args hArgs =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log1_of_nativeEvalArgs
          name expected reservedNames nextSwitchId args native finalSwitchId
          dispatcher nativeStmt hArgs hLower hMem
  | expr_log2 args hArgs =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log2_of_nativeEvalArgs
          name expected reservedNames nextSwitchId args native finalSwitchId
          dispatcher nativeStmt hArgs hLower hMem
  | expr_log3 args hArgs =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log3_of_nativeEvalArgs
          name expected reservedNames nextSwitchId args native finalSwitchId
          dispatcher nativeStmt hArgs hLower hMem
  | expr_log4 args hArgs =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_log4_of_nativeEvalArgs
          name expected reservedNames nextSwitchId args native finalSwitchId
          dispatcher nativeStmt hArgs hLower hMem
  | expr_calldatacopy destOffset sourceOffset sizeExpr hDest hSource hSize =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_calldatacopy_of_nativeEvalArgs
          name expected reservedNames nextSwitchId destOffset sourceOffset sizeExpr
          native finalSwitchId dispatcher nativeStmt hDest hSource hSize hLower hMem
  | expr_returndatacopy destOffset sourceOffset sizeExpr hDest hSource hSize =>
      exact
        NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_expr_returndatacopy_of_nativeEvalArgs
          name expected reservedNames nextSwitchId destOffset sourceOffset sizeExpr
          native finalSwitchId dispatcher nativeStmt hDest hSource hSize hLower hMem

theorem NativeStmtPreservesWord_of_mem_lowerStmtsNativeWithSwitchIds_of_nativePreservableStraightStmts
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (stmts : List YulStmt)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hStmts : NativePreservableStraightStmts stmts)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts =
        .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hFresh : (name : String) ∉ Backends.nativeStmtWriteNames nativeStmt) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) := by
  induction stmts generalizing nextSwitchId native finalSwitchId with
  | nil =>
      rw [Backends.lowerStmtsNativeWithSwitchIds_nil] at hLower
      cases hLower
      simp at hMem
  | cons stmt rest ih =>
      rw [Backends.lowerStmtsNativeWithSwitchIds_cons] at hLower
      cases hHeadLower :
          Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId stmt with
      | error err =>
          rw [hHeadLower] at hLower
          simp only [Bind.bind, Except.bind, reduceCtorEq] at hLower
      | ok headPair =>
          rcases headPair with ⟨headNative, midSwitchId⟩
          rw [hHeadLower] at hLower
          simp only [Bind.bind, Except.bind] at hLower
          cases hRestLower :
              Backends.lowerStmtsNativeWithSwitchIds reservedNames midSwitchId rest with
          | error err =>
              rw [hRestLower] at hLower
              simp only [reduceCtorEq] at hLower
          | ok restPair =>
              rcases restPair with ⟨restNative, restSwitchId⟩
              rw [hRestLower] at hLower
              simp only [Pure.pure, Except.pure, Except.ok.injEq,
                Prod.mk.injEq] at hLower
              obtain ⟨hNative, hFinal⟩ := hLower
              subst hNative
              subst hFinal
              rw [List.mem_append] at hMem
              rcases hMem with hMem | hMem
              · exact
                  NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_of_nativePreservableStraightStmt
                    name expected reservedNames nextSwitchId stmt headNative
                    midSwitchId dispatcher nativeStmt
                    (hStmts stmt (by simp)) hHeadLower hMem hFresh
              · exact
                  ih midSwitchId restNative restSwitchId
                    (by
                      intro restStmt hRestMem
                      exact hStmts restStmt (by simp [hRestMem]))
                    hRestLower hMem

theorem NativeStmtPreservesWord_of_mem_lowerStmtsNativeWithSwitchIds_of_bridgedStraightStmts
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (stmts : List YulStmt)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (nativeStmt : EvmYul.Yul.Ast.Stmt)
    (hStmts :
      Compiler.Proofs.YulGeneration.Backends.BridgedStraightStmts stmts)
    (hSide :
      ∀ stmt, stmt ∈ stmts →
        NativePreservableSideConditionForBridgedStraightStmt stmt)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts =
        .ok (native, finalSwitchId))
    (hMem : nativeStmt ∈ native)
    (hFresh : (name : String) ∉ Backends.nativeStmtWriteNames nativeStmt) :
    NativeStmtPreservesWord name expected nativeStmt
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
  NativeStmtPreservesWord_of_mem_lowerStmtsNativeWithSwitchIds_of_nativePreservableStraightStmts
    name expected reservedNames nextSwitchId stmts native finalSwitchId
    dispatcher nativeStmt
    (NativePreservableStraightStmts.of_bridgedStraightStmts hStmts hSide)
    hLower hMem hFresh

theorem NativeBlockPreservesWord_lowerStmtsNativeWithSwitchIds_of_nativePreservableStraightStmts
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (stmts : List YulStmt)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hStmts : NativePreservableStraightStmts stmts)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts =
        .ok (native, finalSwitchId))
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames native) :
    NativeBlockPreservesWord name expected native
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem name expected native
    (some
      { dispatcher := dispatcher
        functions := ((∅ : NativeFunctionMap).insert
          "mappingSlot" nativeMappingSlotFunctionDefinition) })
    hFresh
    (by
      intro nativeStmt hMem hStmtFresh
      exact
        NativeStmtPreservesWord_of_mem_lowerStmtsNativeWithSwitchIds_of_nativePreservableStraightStmts
          name expected reservedNames nextSwitchId stmts native finalSwitchId
          dispatcher nativeStmt hStmts hLower hMem hStmtFresh)

/-- Lowered straight bridged statement lists preserve a marker word under the
native EVMYulLean harness, once the small native-preservation side conditions
are supplied.

This packages the historical bridged-straight predicate conversion together
with the native lowering preservation theorem. Selector-hit success proofs can
use this directly after extracting no-write freshness for the selected lowered
body. -/
theorem NativeBlockPreservesWord_lowerStmtsNativeWithSwitchIds_of_bridgedStraightStmts
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (stmts : List YulStmt)
    (native : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (dispatcher : EvmYul.Yul.Ast.Stmt)
    (hStmts :
      Compiler.Proofs.YulGeneration.Backends.BridgedStraightStmts stmts)
    (hSide :
      ∀ stmt, stmt ∈ stmts →
        NativePreservableSideConditionForBridgedStraightStmt stmt)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts =
        .ok (native, finalSwitchId))
    (hFresh : (name : String) ∉ Backends.nativeStmtsWriteNames native) :
    NativeBlockPreservesWord name expected native
      (some
        { dispatcher := dispatcher
          functions := ((∅ : NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) }) :=
  NativeBlockPreservesWord_lowerStmtsNativeWithSwitchIds_of_nativePreservableStraightStmts
    name expected reservedNames nextSwitchId stmts native finalSwitchId
    dispatcher
    (NativePreservableStraightStmts.of_bridgedStraightStmts hStmts hSide)
    hLower hFresh

theorem nativeSwitchTempsFreshForNativeBodies_case_matched_not_mem
    (switchId tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hMem : (tag, body) ∈ cases) :
    Backends.nativeSwitchMatchedTempName switchId ∉
      Backends.nativeStmtsWriteNames body :=
  (hFresh.1 tag body hMem).2

theorem nativeSwitchTempsFreshForNativeBodies_case_discr_not_mem
    (switchId tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hMem : (tag, body) ∈ cases) :
    Backends.nativeSwitchDiscrTempName switchId ∉
      Backends.nativeStmtsWriteNames body :=
  (hFresh.1 tag body hMem).1

theorem nativeSwitchTempsFreshForNativeBodies_find_hit_matched_not_mem
    (switchId selector tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body)) :
    Backends.nativeSwitchMatchedTempName switchId ∉
      Backends.nativeStmtsWriteNames body := by
  have hMem : (tag, body) ∈ cases := by
    clear hFresh
    induction cases with
    | nil =>
        simp [List.find?] at hFind
    | cons head rest ih =>
        cases hHead : (head.1 == selector)
        · simp [List.find?, hHead] at hFind
          exact List.mem_cons_of_mem head (ih hFind)
        · simp [List.find?, hHead] at hFind
          simp [hFind]
  exact nativeSwitchTempsFreshForNativeBodies_case_matched_not_mem
    switchId tag body defaultBody cases hFresh hMem

theorem nativeSwitchTempsFreshForNativeBodies_find_hit_discr_not_mem
    (switchId selector tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body)) :
    Backends.nativeSwitchDiscrTempName switchId ∉
      Backends.nativeStmtsWriteNames body := by
  have hMem : (tag, body) ∈ cases := by
    clear hFresh
    induction cases with
    | nil =>
        simp [List.find?] at hFind
    | cons head rest ih =>
        cases hHead : (head.1 == selector)
        · simp [List.find?, hHead] at hFind
          exact List.mem_cons_of_mem head (ih hFind)
        · simp [List.find?, hHead] at hFind
          simp [hFind]
  exact nativeSwitchTempsFreshForNativeBodies_case_discr_not_mem
    switchId tag body defaultBody cases hFresh hMem

theorem nativeSwitchTempsFreshForNativeBodies_default_matched_not_mem
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody) :
    Backends.nativeSwitchMatchedTempName switchId ∉
      Backends.nativeStmtsWriteNames defaultBody :=
  hFresh.2.2

theorem nativeSwitchTempsFreshForNativeBodies_default_discr_not_mem
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody) :
    Backends.nativeSwitchDiscrTempName switchId ∉
      Backends.nativeStmtsWriteNames defaultBody :=
  hFresh.2.1

theorem NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_matched
    (switchId selector tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          expected stmt codeOverride) :
    NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
      expected body codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (Backends.nativeSwitchMatchedTempName switchId) expected body codeOverride
    (nativeSwitchTempsFreshForNativeBodies_find_hit_matched_not_mem
      switchId selector tag body defaultBody cases hFresh hFind)
    hStmtPreserves

theorem NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_discr
    (switchId selector tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchDiscrTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchDiscrTempName switchId)
          expected stmt codeOverride) :
    NativeBlockPreservesWord (Backends.nativeSwitchDiscrTempName switchId)
      expected body codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (Backends.nativeSwitchDiscrTempName switchId) expected body codeOverride
    (nativeSwitchTempsFreshForNativeBodies_find_hit_discr_not_mem
      switchId selector tag body defaultBody cases hFresh hFind)
    hStmtPreserves

theorem NativeBlockPreservesWord_of_nativeSwitchFresh_default_matched
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ defaultBody →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          expected stmt codeOverride) :
    NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
      expected defaultBody codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (Backends.nativeSwitchMatchedTempName switchId) expected defaultBody
    codeOverride
    (nativeSwitchTempsFreshForNativeBodies_default_matched_not_mem
      switchId cases defaultBody hFresh)
    hStmtPreserves

theorem NativeBlockPreservesWord_of_nativeSwitchFresh_default_discr
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ defaultBody →
        Backends.nativeSwitchDiscrTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchDiscrTempName switchId)
          expected stmt codeOverride) :
    NativeBlockPreservesWord (Backends.nativeSwitchDiscrTempName switchId)
      expected defaultBody codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (Backends.nativeSwitchDiscrTempName switchId) expected defaultBody
    codeOverride
    (nativeSwitchTempsFreshForNativeBodies_default_discr_not_mem
      switchId cases defaultBody hFresh)
    hStmtPreserves

@[simp] theorem nativeSwitchCaseIfs_nil
    (discrName matchedName : EvmYul.Identifier) :
    nativeSwitchCaseIfs discrName matchedName [] = [] := by
  rfl

@[simp] theorem nativeSwitchCaseIfs_cons
    (discrName matchedName : EvmYul.Identifier)
    (entry : Nat × List EvmYul.Yul.Ast.Stmt)
    (rest : List (Nat × List EvmYul.Yul.Ast.Stmt)) :
    nativeSwitchCaseIfs discrName matchedName (entry :: rest) =
      nativeSwitchCaseIf discrName matchedName entry ::
        nativeSwitchCaseIfs discrName matchedName rest := by
  rfl

private theorem list_find?_eq_some_split_false
    {α : Type}
    (p : α → Bool) :
    ∀ {xs : List α} {x : α},
      xs.find? p = some x →
        ∃ pre suffix,
          xs = pre ++ x :: suffix ∧
          ∀ y, y ∈ pre → p y = false
  | [], _, hFind => by
      simp [List.find?] at hFind
  | y :: ys, x, hFind => by
      by_cases hp : p y = true
      · have hxy : x = y := by
          simpa [List.find?, hp] using hFind.symm
        subst x
        exact ⟨[], ys, by simp, by simp⟩
      · have hFalse : p y = false := Bool.eq_false_iff.2 hp
        have hRest : ys.find? p = some x := by
          simpa [List.find?, hFalse] using hFind
        rcases list_find?_eq_some_split_false p hRest with
          ⟨pre, suffix, hSplit, hPre⟩
        refine ⟨y :: pre, suffix, ?_, ?_⟩
        · simp [hSplit]
        · intro z hz
          have hz' : z = y ∨ z ∈ pre := by
            simpa [List.mem_cons] using hz
          rcases hz' with hzy | hzPre
          · cases hzy
            exact hFalse
          · exact hPre z hzPre

private theorem list_find?_eq_none_all_false
    {α : Type}
    (p : α → Bool) :
    ∀ {xs : List α},
      xs.find? p = none →
        ∀ x, x ∈ xs → p x = false
  | [], hFind, x, hx => by
      simp at hx
  | y :: ys, hFind, x, hx => by
      by_cases hp : p y = true
      · simp [List.find?, hp] at hFind
      · have hFalse : p y = false := Bool.eq_false_iff.2 hp
        have hRest : ys.find? p = none := by
          simpa [List.find?, hFalse] using hFind
        have hx' : x = y ∨ x ∈ ys := by
          simpa [List.mem_cons] using hx
        rcases hx' with hxy | hxTail
        · cases hxy
          exact hFalse
        · exact list_find?_eq_none_all_false p hRest x hxTail

private theorem uint256_ofNat_ne_of_ne_of_lt
    {a b : Nat}
    (ha : a < EvmYul.UInt256.size)
    (hb : b < EvmYul.UInt256.size)
    (hne : a ≠ b) :
    EvmYul.UInt256.ofNat a ≠ EvmYul.UInt256.ofNat b := by
  intro h
  apply hne
  have hToNat := congrArg EvmYul.UInt256.toNat h
  rw [uint256_ofNat_toNat_of_lt a ha,
    uint256_ofNat_toNat_of_lt b hb] at hToNat
  exact hToNat

private theorem nativeSwitch_prefix_miss_of_selector_find
    (selector : Nat)
    (cases pre suffix : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (state : EvmYul.Yul.State)
    (discrName : EvmYul.Identifier)
    (hCases : cases = pre ++ (tag, body) :: suffix)
    (hPrefix :
      ∀ entry, entry ∈ pre → (fun entry : Nat × List EvmYul.Yul.Ast.Stmt =>
        entry.1 == selector) entry = false)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size) :
    ∀ tag' body', (tag', body') ∈ pre →
      state[discrName]! ≠ EvmYul.UInt256.ofNat tag' := by
  intro tag' body' hmem hDiscrTag
  have hPrefixFalse := hPrefix (tag', body') hmem
  have hTagNe : tag' ≠ selector := by
    intro hEq
    have hTrue : (tag' == selector) = true := beq_iff_eq.mpr hEq
    have hFalse : (tag' == selector) = false := by
      simpa using hPrefixFalse
    rw [hTrue] at hFalse
    contradiction
  have hCaseMem : (tag', body') ∈ cases := by
    rw [hCases]
    simp [hmem]
  have hWordNe :
      EvmYul.UInt256.ofNat selector ≠ EvmYul.UInt256.ofNat tag' :=
    uint256_ofNat_ne_of_ne_of_lt hSelectorRange
      (hTagsRange tag' body' hCaseMem) (Ne.symm hTagNe)
  exact hWordNe (hDiscrSelector.symm.trans hDiscrTag)

/-- A selector lookup hit exposes the generated case list as a miss prefix,
    selected case, and suffix. This is the list-shape bridge consumed by the
    native lazy-switch execution lemmas. -/
theorem nativeSwitch_find_hit_split
    (selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = some (tag, body)) :
    ∃ pre suffix,
      cases = pre ++ (tag, body) :: suffix ∧
      tag = selector ∧
      ∀ entry, entry ∈ pre →
        (fun entry : Nat × List EvmYul.Yul.Ast.Stmt =>
          entry.1 == selector) entry = false := by
  rcases list_find?_eq_some_split_false
      (fun entry : Nat × List EvmYul.Yul.Ast.Stmt => entry.1 == selector)
      hFind with
    ⟨pre, suffix, hSplit, hPrefix⟩
  have hSelected :
      (fun entry : Nat × List EvmYul.Yul.Ast.Stmt =>
        entry.1 == selector) (tag, body) = true :=
    List.find?_some
      (p := fun entry : Nat × List EvmYul.Yul.Ast.Stmt =>
        entry.1 == selector) hFind
  have hTag : tag = selector := by
    exact beq_iff_eq.mp hSelected
  exact ⟨pre, suffix, hSplit, hTag, hPrefix⟩

/-- A selector lookup miss proves every generated case tag misses the native
    dispatcher discriminator when the discriminator contains that selector and
    all case tags are in the `UInt256` range. -/
theorem nativeSwitch_find_none_all_miss
    (selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (state : EvmYul.Yul.State)
    (discrName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = none)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    ∀ tag body, (tag, body) ∈ cases →
      state[discrName]! ≠ EvmYul.UInt256.ofNat tag := by
  intro tag body hmem hDiscrTag
  have hFalse :=
    list_find?_eq_none_all_false
      (fun entry : Nat × List EvmYul.Yul.Ast.Stmt => entry.1 == selector)
      hFind (tag, body) hmem
  have hTagNe : tag ≠ selector := by
    intro hEq
    have hTrue : (tag == selector) = true := beq_iff_eq.mpr hEq
    have hFalse' : (tag == selector) = false := by
      simpa using hFalse
    rw [hTrue] at hFalse'
    contradiction
  have hWordNe :
      EvmYul.UInt256.ofNat selector ≠ EvmYul.UInt256.ofNat tag :=
    uint256_ofNat_ne_of_ne_of_lt hSelectorRange
      (hTagsRange tag body hmem) (Ne.symm hTagNe)
  exact hWordNe (hDiscrSelector.symm.trans hDiscrTag)

/-- If no case tag matches and the matched flag is still clear, the generated
    native switch case chain skips every case body and leaves the state
    unchanged. -/
theorem exec_nativeSwitchCaseIfs_all_miss_fuel
    (fuel : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hMiss :
      ∀ tag body, (tag, body) ∈ cases →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .ok state := by
  induction cases generalizing fuel codeOverride state discrName matchedName with
  | nil =>
      simp [nativeSwitchCaseIfs, EvmYul.Yul.exec]
  | cons entry rest ih =>
      rcases entry with ⟨tag, body⟩
      have hHeadMiss : state[discrName]! ≠ EvmYul.UInt256.ofNat tag := by
        exact hMiss tag body (by simp)
      have hRestMiss :
          ∀ tag' body', (tag', body') ∈ rest →
            state[discrName]! ≠ EvmYul.UInt256.ofNat tag' := by
        intro tag' body' hmem
        exact hMiss tag' body' (by simp [hmem])
      have hHead :
          EvmYul.Yul.exec (fuel + rest.length + 9)
            (nativeSwitchCaseIf discrName matchedName (tag, body))
            codeOverride state = .ok state := by
        simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
          (exec_if_nativeSwitchGuardedMatch_miss_fuel
            (fuel + rest.length) (Backends.lowerAssignNative matchedName (.lit 1) :: body)
            codeOverride state discrName matchedName tag hMatched hHeadMiss)
      have hTail :
          EvmYul.Yul.exec (fuel + rest.length + 9)
            (.Block (nativeSwitchCaseIfs discrName matchedName rest))
            codeOverride state = .ok state :=
        ih fuel codeOverride state discrName matchedName hMatched hRestMiss
      have hBlock := exec_block_cons_ok (fuel + rest.length + 9)
        (nativeSwitchCaseIf discrName matchedName (tag, body))
        (nativeSwitchCaseIfs discrName matchedName rest)
        codeOverride state state state hHead hTail
      simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hBlock

/-- Once a selected lowered switch body preserves the matched flag at one, every
    later generated case guard skips. -/
theorem exec_nativeSwitchCaseIfs_matched_fuel
    (fuel : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .ok state := by
  induction cases generalizing fuel codeOverride state discrName matchedName with
  | nil =>
      simp [nativeSwitchCaseIfs, EvmYul.Yul.exec]
  | cons entry rest ih =>
      rcases entry with ⟨tag, body⟩
      have hHead :
          EvmYul.Yul.exec (fuel + rest.length + 9)
            (nativeSwitchCaseIf discrName matchedName (tag, body))
            codeOverride state = .ok state := by
        simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
          (exec_if_nativeSwitchGuardedMatch_matched_fuel
            (fuel + rest.length) (Backends.lowerAssignNative matchedName (.lit 1) :: body)
            codeOverride state discrName matchedName tag hMatched)
      have hTail :
          EvmYul.Yul.exec (fuel + rest.length + 9)
            (.Block (nativeSwitchCaseIfs discrName matchedName rest))
            codeOverride state = .ok state :=
        ih fuel codeOverride state discrName matchedName hMatched
      have hBlock := exec_block_cons_ok (fuel + rest.length + 9)
        (nativeSwitchCaseIf discrName matchedName (tag, body))
        (nativeSwitchCaseIfs discrName matchedName rest)
        codeOverride state state state hHead hTail
      simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hBlock

/-- Whole generated case-chain execution when the first remaining case is the
    selected case and suffix cases must skip after the selected body preserves
    the matched flag. -/
theorem exec_nativeSwitchCaseIfs_head_hit_fuel
    (fuel : Nat)
    (suffix : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .ok final)
    (hFinalMatched : final[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + suffix.length + 10)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName ((tag, body) :: suffix)))
      codeOverride state = .ok final := by
  have hHead :
      EvmYul.Yul.exec (fuel + suffix.length + 9)
        (nativeSwitchCaseIf discrName matchedName (tag, body))
        codeOverride state = .ok final := by
    simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
      (exec_if_nativeSwitchGuardedMatch_hit_marked_fuel
        (fuel + suffix.length) body codeOverride state final discrName
        matchedName tag hMatched hDiscr hBody)
  have hTail :
      EvmYul.Yul.exec (fuel + suffix.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName suffix))
        codeOverride final = .ok final :=
    exec_nativeSwitchCaseIfs_matched_fuel fuel suffix codeOverride final
      discrName matchedName hFinalMatched
  have hBlock := exec_block_cons_ok (fuel + suffix.length + 9)
    (nativeSwitchCaseIf discrName matchedName (tag, body))
    (nativeSwitchCaseIfs discrName matchedName suffix)
    codeOverride state final final hHead hTail
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hBlock

/-- Whole generated case-chain execution when the first remaining case is the
    selected case and that selected body halts or errors before the suffix can
    run. -/
theorem exec_nativeSwitchCaseIfs_head_hit_error_fuel
    (fuel : Nat)
    (suffix : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + suffix.length + 10)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName ((tag, body) :: suffix)))
      codeOverride state = .error err := by
  have hHead :
      EvmYul.Yul.exec (fuel + suffix.length + 9)
        (nativeSwitchCaseIf discrName matchedName (tag, body))
        codeOverride state = .error err := by
    simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
      (exec_if_nativeSwitchGuardedMatch_hit_marked_error_fuel
        (fuel + suffix.length) body codeOverride state discrName matchedName
        tag err hMatched hDiscr hBody)
  have hBlock :=
    exec_block_cons_error (fuel + suffix.length + 9)
      (nativeSwitchCaseIf discrName matchedName (tag, body))
      (nativeSwitchCaseIfs discrName matchedName suffix)
      codeOverride state err hHead
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hBlock

/-- Cons a non-selected generated switch case onto an already-proved generated
    case-chain execution. -/
theorem exec_nativeSwitchCaseIfs_cons_miss_fuel
    (fuel : Nat)
    (rest : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (missTag : Nat)
    (missBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hHeadMiss : state[discrName]! ≠ EvmYul.UInt256.ofNat missTag)
    (hTail :
      EvmYul.Yul.exec (fuel + rest.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName rest))
        codeOverride state = .ok final) :
    EvmYul.Yul.exec (fuel + rest.length + 10)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName
          ((missTag, missBody) :: rest)))
      codeOverride state = .ok final := by
  have hHead :
      EvmYul.Yul.exec (fuel + rest.length + 9)
        (nativeSwitchCaseIf discrName matchedName (missTag, missBody))
        codeOverride state = .ok state := by
    simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
      (exec_if_nativeSwitchGuardedMatch_miss_fuel
        (fuel + rest.length)
        (Backends.lowerAssignNative matchedName (.lit 1) :: missBody)
        codeOverride state discrName matchedName missTag hMatched hHeadMiss)
  have hBlock := exec_block_cons_ok (fuel + rest.length + 9)
    (nativeSwitchCaseIf discrName matchedName (missTag, missBody))
    (nativeSwitchCaseIfs discrName matchedName rest)
    codeOverride state state final hHead hTail
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hBlock

/-- Whole generated case-chain execution for a miss prefix, selected case, and suffix. -/
theorem exec_nativeSwitchCaseIfs_prefix_hit_fuel
    (fuel : Nat)
    (pre suffix : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat) (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hMissPrefix : ∀ tag' body', (tag', body') ∈ pre →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag')
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .ok final)
    (hFinalMatched : final[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + (pre ++ (tag, body) :: suffix).length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName
        (pre ++ (tag, body) :: suffix)))
      codeOverride state = .ok final := by
  induction pre generalizing fuel with
  | nil =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exec_nativeSwitchCaseIfs_head_hit_fuel fuel suffix tag body codeOverride
          state final discrName matchedName hMatched hDiscr hBody hFinalMatched)
  | cons entry rest ih =>
      rcases entry with ⟨missTag, missBody⟩
      have hHeadMiss :
          state[discrName]! ≠ EvmYul.UInt256.ofNat missTag := by
        exact hMissPrefix missTag missBody (by simp)
      have hRestMiss :
          ∀ tag' body', (tag', body') ∈ rest →
            state[discrName]! ≠ EvmYul.UInt256.ofNat tag' := by
        intro tag' body' hmem
        exact hMissPrefix tag' body' (by simp [hmem])
      have hTail :
          EvmYul.Yul.exec
            (fuel + (rest ++ (tag, body) :: suffix).length + 9)
            (.Block (nativeSwitchCaseIfs discrName matchedName
              (rest ++ (tag, body) :: suffix)))
            codeOverride state = .ok final :=
        ih fuel hRestMiss hBody
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exec_nativeSwitchCaseIfs_cons_miss_fuel fuel
          (rest ++ (tag, body) :: suffix) missTag missBody codeOverride state
          final discrName matchedName hMatched hHeadMiss hTail)

/-- Whole generated case-chain execution for a miss prefix, selected case, and
    suffix when the selected case halts or errors. -/
theorem exec_nativeSwitchCaseIfs_prefix_hit_error_fuel
    (fuel : Nat)
    (pre suffix : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat) (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hMissPrefix : ∀ tag' body', (tag', body') ∈ pre →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag')
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + (pre ++ (tag, body) :: suffix).length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName
        (pre ++ (tag, body) :: suffix)))
      codeOverride state = .error err := by
  induction pre generalizing fuel with
  | nil =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exec_nativeSwitchCaseIfs_head_hit_error_fuel fuel suffix tag body
          codeOverride state discrName matchedName err hMatched hDiscr hBody)
  | cons entry rest ih =>
      rcases entry with ⟨missTag, missBody⟩
      have hHeadMiss :
          state[discrName]! ≠ EvmYul.UInt256.ofNat missTag := by
        exact hMissPrefix missTag missBody (by simp)
      have hRestMiss :
          ∀ tag' body', (tag', body') ∈ rest →
            state[discrName]! ≠ EvmYul.UInt256.ofNat tag' := by
        intro tag' body' hmem
        exact hMissPrefix tag' body' (by simp [hmem])
      have hTail :
          EvmYul.Yul.exec
            (fuel + (rest ++ (tag, body) :: suffix).length + 9)
            (.Block (nativeSwitchCaseIfs discrName matchedName
              (rest ++ (tag, body) :: suffix)))
            codeOverride state = .error err :=
        ih fuel hRestMiss hBody
      have hHead :
          EvmYul.Yul.exec
            (fuel + (rest ++ (tag, body) :: suffix).length + 9)
            (nativeSwitchCaseIf discrName matchedName (missTag, missBody))
            codeOverride state = .ok state := by
        simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
          (exec_if_nativeSwitchGuardedMatch_miss_fuel
            (fuel + (rest ++ (tag, body) :: suffix).length)
            (Backends.lowerAssignNative matchedName (.lit 1) :: missBody)
            codeOverride state discrName matchedName missTag hMatched hHeadMiss)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exec_block_cons_tail_error
          (fuel + (rest ++ (tag, body) :: suffix).length + 9)
          (nativeSwitchCaseIf discrName matchedName (missTag, missBody))
          (nativeSwitchCaseIfs discrName matchedName
            (rest ++ (tag, body) :: suffix))
          codeOverride state state err hHead hTail)

/-- Whole generated case-chain execution for a selector lookup hit. This wraps
    `exec_nativeSwitchCaseIfs_prefix_hit_fuel` with the generated dispatcher
    lookup split, so callers only need the `find?` result and the selected body
    execution premise for the discovered suffix. -/
theorem exec_nativeSwitchCaseIfs_find_hit_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody :
      ∀ pre suffix,
        cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body)
            codeOverride (state.insert matchedName (EvmYul.UInt256.ofNat 1)) =
            .ok final)
    (hFinalMatched : final[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .ok final := by
  rcases nativeSwitch_find_hit_split selector cases tag body hFind with
    ⟨pre, suffix, hCases, hTag, hPrefix⟩
  subst tag
  have hMissPrefix :
      ∀ tag' body', (tag', body') ∈ pre →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag' :=
    nativeSwitch_prefix_miss_of_selector_find selector cases pre suffix selector body
      state discrName hCases hPrefix hDiscrSelector hSelectorRange hTagsRange
  have hSelectedBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body)
        codeOverride (state.insert matchedName (EvmYul.UInt256.ofNat 1)) =
        .ok final :=
    hBody pre suffix hCases
  have hExec :=
    exec_nativeSwitchCaseIfs_prefix_hit_fuel fuel pre suffix selector body
      codeOverride state final discrName matchedName hMatched hMissPrefix
      hDiscrSelector hSelectedBody hFinalMatched
  simpa [hCases, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hExec

/-- Whole generated case-chain execution for a selector lookup hit whose
    selected body halts or errors. -/
theorem exec_nativeSwitchCaseIfs_find_hit_error_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody :
      ∀ pre suffix,
        cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body)
            codeOverride (state.insert matchedName (EvmYul.UInt256.ofNat 1)) =
            .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .error err := by
  rcases nativeSwitch_find_hit_split selector cases tag body hFind with
    ⟨pre, suffix, hCases, hTag, hPrefix⟩
  subst tag
  have hMissPrefix :
      ∀ tag' body', (tag', body') ∈ pre →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag' :=
    nativeSwitch_prefix_miss_of_selector_find selector cases pre suffix selector body
      state discrName hCases hPrefix hDiscrSelector hSelectorRange hTagsRange
  have hSelectedBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body)
        codeOverride (state.insert matchedName (EvmYul.UInt256.ofNat 1)) =
        .error err :=
    hBody pre suffix hCases
  have hExec :=
    exec_nativeSwitchCaseIfs_prefix_hit_error_fuel fuel pre suffix selector body
      codeOverride state discrName matchedName err hMatched hMissPrefix
      hDiscrSelector hSelectedBody
  simpa [hCases, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hExec

/-- Selector-hit case-chain execution with the selected-body matched-flag
    preservation obligation factored into a reusable predicate.

This is the proof boundary needed by the full native dispatcher bridge: the
lowered case body may update storage, memory, and user variables, but it must
not clobber the generated lazy-switch matched flag after the lowering has set
it to one. -/
theorem exec_nativeSwitchCaseIfs_find_hit_preserved_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hMarked :
      (state.insert matchedName (EvmYul.UInt256.ofNat 1))[matchedName]! =
        EvmYul.UInt256.ofNat 1)
    (hBody :
      ∀ pre suffix,
        cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body)
            codeOverride (state.insert matchedName (EvmYul.UInt256.ofNat 1)) =
            .ok final)
    (hPreservesMatched :
      ∀ pre suffix,
        cases = pre ++ (tag, body) :: suffix →
          NativeBlockPreservesWord matchedName (EvmYul.UInt256.ofNat 1)
            body codeOverride) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .ok final := by
  apply exec_nativeSwitchCaseIfs_find_hit_fuel
      (fuel := fuel) (selector := selector) (cases := cases) (tag := tag)
      (body := body) (codeOverride := codeOverride) (state := state)
      (final := final) (discrName := discrName) (matchedName := matchedName)
      hFind hMatched hDiscrSelector hSelectorRange hTagsRange hBody
  rcases nativeSwitch_find_hit_split selector cases tag body hFind with
    ⟨pre, suffix, hCases, _hTag, _hPrefix⟩
  exact hPreservesMatched pre suffix hCases (fuel + suffix.length + 7)
    (state.insert matchedName (EvmYul.UInt256.ofNat 1)) final hMarked
    (hBody pre suffix hCases)

/-- Whole generated case-chain skip for a selector lookup miss. This packages
    the `find? = none` selector fact into the all-cases-miss premise expected by
    the lazy native switch executor. -/
theorem exec_nativeSwitchCaseIfs_find_none_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = none)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .ok state := by
  have hMiss :
      ∀ tag body, (tag, body) ∈ cases →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag :=
    nativeSwitch_find_none_all_miss selector cases state discrName hFind
      hDiscrSelector hSelectorRange hTagsRange
  exact exec_nativeSwitchCaseIfs_all_miss_fuel fuel cases codeOverride state
    discrName matchedName hMatched hMiss
/-- Non-empty generated default block execution when no case matched. -/
theorem exec_nativeSwitchDefaultIf_unmatched_nonempty_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody :
      EvmYul.Yul.exec (fuel + 6) (.Block defaultBody) codeOverride state =
        .ok final)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + 8)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok final := by
  cases defaultBody with
  | nil => contradiction
  | cons stmt rest =>
      have hHead :
          EvmYul.Yul.exec (fuel + 7)
            (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
            codeOverride state = .ok final := by
        simpa [nativeSwitchDefaultGuardExpr] using
          (exec_if_nativeSwitchDefaultGuard_unmatched_fuel fuel
            (stmt :: rest) codeOverride state final matchedName hMatched hBody)
      have hTail :
          EvmYul.Yul.exec (fuel + 7) (.Block [])
            codeOverride final = .ok final := by
        simp [EvmYul.Yul.exec]
      exact exec_block_cons_ok (fuel + 7)
        (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
        [] codeOverride state final final hHead hTail

/-- Non-empty generated default block execution when no case matched and the
    default body halts or errors. This is the selector-miss path used by a
    default `revert(0, 0)` body. -/
theorem exec_nativeSwitchDefaultIf_unmatched_nonempty_error_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody :
      EvmYul.Yul.exec (fuel + 6) (.Block defaultBody) codeOverride state =
        .error err)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + 8)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .error err := by
  cases defaultBody with
  | nil => contradiction
  | cons stmt rest =>
      have hHead :
          EvmYul.Yul.exec (fuel + 7)
            (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
            codeOverride state = .error err := by
        simpa [nativeSwitchDefaultGuardExpr] using
          (exec_if_nativeSwitchDefaultGuard_unmatched_error_fuel fuel
            (stmt :: rest) codeOverride state matchedName err hMatched hBody)
      exact exec_block_cons_error (fuel + 7)
        (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
        [] codeOverride state err hHead

/-- After a selected case preserves the matched flag at one, the optional
    generated default block skips. Empty defaults also skip because no default
    statement is emitted. -/
theorem exec_nativeSwitchDefaultIf_matched_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec
      (fuel + (nativeSwitchDefaultIf matchedName defaultBody).length + 7)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok state := by
  cases defaultBody with
  | nil =>
      simp [nativeSwitchDefaultIf, EvmYul.Yul.exec]
  | cons stmt rest =>
      have hHead :
          EvmYul.Yul.exec (fuel + 7)
            (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
            codeOverride state = .ok state := by
        simpa [nativeSwitchDefaultGuardExpr] using
          (exec_if_nativeSwitchDefaultGuard_matched_fuel fuel
            (stmt :: rest) codeOverride state matchedName hMatched)
      have hTail :
          EvmYul.Yul.exec (fuel + 7) (.Block [])
            codeOverride state = .ok state := by
        simp [EvmYul.Yul.exec]
      simpa [nativeSwitchDefaultIf] using
        (exec_block_cons_ok (fuel + 7)
          (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
          [] codeOverride state state state hHead hTail)

/-- Default-tail skip at the fuel level left after a generated case chain. -/
theorem exec_nativeSwitchDefaultIf_matched_caseTail_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 9)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok state := by
  cases defaultBody with
  | nil =>
      simp [nativeSwitchDefaultIf, EvmYul.Yul.exec]
  | cons stmt rest =>
      simpa [nativeSwitchDefaultIf, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        (exec_nativeSwitchDefaultIf_matched_fuel (fuel + 1)
          (stmt :: rest) codeOverride state matchedName hMatched)

/-- Non-empty default-tail execution at the fuel level left after all generated
    cases miss. -/
theorem exec_nativeSwitchDefaultIf_unmatched_caseTail_nonempty_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody :
      EvmYul.Yul.exec (fuel + 7) (.Block defaultBody) codeOverride state =
        .ok final)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + 9)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok final := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exec_nativeSwitchDefaultIf_unmatched_nonempty_fuel (fuel + 1)
      defaultBody codeOverride state final matchedName hMatched hBody hNonempty)

/-- Non-empty default-tail error execution at the fuel level left after all
    generated cases miss. -/
theorem exec_nativeSwitchDefaultIf_unmatched_caseTail_nonempty_error_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody :
      EvmYul.Yul.exec (fuel + 7) (.Block defaultBody) codeOverride state =
        .error err)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + 9)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .error err := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exec_nativeSwitchDefaultIf_unmatched_nonempty_error_fuel (fuel + 1)
      defaultBody codeOverride state matchedName err hMatched hBody hNonempty)

/-- Compose a generated case chain with its optional default when the case chain
    has already set and preserved the matched flag. -/
theorem exec_nativeSwitchCaseIfs_with_default_matched_fuel
    (fuel : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .ok final)
    (hFinalMatched : final[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok final := by
  have hDefault :
      EvmYul.Yul.exec (fuel + 9)
        (.Block (nativeSwitchDefaultIf matchedName defaultBody))
        codeOverride final = .ok final :=
    exec_nativeSwitchDefaultIf_matched_caseTail_fuel fuel defaultBody
      codeOverride final matchedName hFinalMatched
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using exec_block_append_ok fuel 9
      (nativeSwitchCaseIfs discrName matchedName cases)
      (nativeSwitchDefaultIf matchedName defaultBody)
      codeOverride state final final
      (by simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hCases)
      hDefault

/-- Checkpoint-specialized form of `exec_nativeSwitchCaseIfs_matched_fuel`.
    Checkpoint lookup reads the jump store, so a matched flag already set to one
    makes every generated suffix case a no-op without reviving the raw state. -/
theorem exec_nativeSwitchCaseIfs_checkpoint_matched_fuel
    (fuel : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (jump : EvmYul.Yul.Jump)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched :
      (EvmYul.Yul.State.Checkpoint jump)[matchedName]! =
        EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride (EvmYul.Yul.State.Checkpoint jump) =
        .ok (EvmYul.Yul.State.Checkpoint jump) :=
  exec_nativeSwitchCaseIfs_matched_fuel fuel cases codeOverride
    (EvmYul.Yul.State.Checkpoint jump) discrName matchedName hMatched

/-- Checkpoint-specialized form of `exec_nativeSwitchDefaultIf_matched_caseTail_fuel`.
    The generated default tail is skipped directly on the raw checkpoint when
    the checkpoint store records the matched flag as one. -/
theorem exec_nativeSwitchDefaultIf_checkpoint_matched_caseTail_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (jump : EvmYul.Yul.Jump)
    (matchedName : EvmYul.Identifier)
    (hMatched :
      (EvmYul.Yul.State.Checkpoint jump)[matchedName]! =
        EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 9)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride (EvmYul.Yul.State.Checkpoint jump) =
        .ok (EvmYul.Yul.State.Checkpoint jump) :=
  exec_nativeSwitchDefaultIf_matched_caseTail_fuel fuel defaultBody
    codeOverride (EvmYul.Yul.State.Checkpoint jump) matchedName hMatched

/-- Checkpoint-specialized no-op for the generated case suffix plus optional
    default tail. This is the raw-state counterpart to the revived dispatcher
    projection: the tail does not change the checkpoint before projection. -/
theorem exec_nativeSwitchCaseIfs_with_default_checkpoint_matched_fuel
    (fuel : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (jump : EvmYul.Yul.Jump)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched :
      (EvmYul.Yul.State.Checkpoint jump)[matchedName]! =
        EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride (EvmYul.Yul.State.Checkpoint jump) =
        .ok (EvmYul.Yul.State.Checkpoint jump) := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride (EvmYul.Yul.State.Checkpoint jump) =
          .ok (EvmYul.Yul.State.Checkpoint jump) :=
    exec_nativeSwitchCaseIfs_checkpoint_matched_fuel fuel cases codeOverride
      jump discrName matchedName hMatched
  exact exec_nativeSwitchCaseIfs_with_default_matched_fuel fuel cases
    defaultBody codeOverride (EvmYul.Yul.State.Checkpoint jump)
    (EvmYul.Yul.State.Checkpoint jump) discrName matchedName hCases hMatched

/-- Selector-hit execution for the generated case chain followed by the
    generated optional default statement list. The selected body must preserve
    the matched flag so the default guard and suffix cases skip. -/
theorem exec_nativeSwitchCaseIfs_find_hit_with_default_preserved_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt) (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hMarked : (state.insert matchedName (EvmYul.UInt256.ofNat 1))[matchedName]! =
      EvmYul.UInt256.ofNat 1)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .ok final)
    (hPreservesMatched : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      NativeBlockPreservesWord matchedName (EvmYul.UInt256.ofNat 1) body codeOverride) :
    EvmYul.Yul.exec (fuel + cases.length + 9) (.Block
      (nativeSwitchCaseIfs discrName matchedName cases ++ nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok final := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .ok final :=
    exec_nativeSwitchCaseIfs_find_hit_preserved_fuel fuel selector cases tag
      body codeOverride state final discrName matchedName hFind hMatched
      hDiscrSelector hSelectorRange hTagsRange hMarked hBody hPreservesMatched
  have hFinalMatched : final[matchedName]! = EvmYul.UInt256.ofNat 1 := by
    rcases nativeSwitch_find_hit_split selector cases tag body hFind with
      ⟨pre, suffix, hCasesEq, _hTag, _hPrefix⟩
    exact hPreservesMatched pre suffix hCasesEq
      (fuel + suffix.length + 7)
      (state.insert matchedName (EvmYul.UInt256.ofNat 1)) final hMarked
      (hBody pre suffix hCasesEq)
  exact exec_nativeSwitchCaseIfs_with_default_matched_fuel fuel cases
    defaultBody codeOverride state final discrName matchedName hCases
    hFinalMatched

/-- Selector-hit execution for the generated case chain followed by the
    generated optional default statement list when the selected case halts or
    errors. The default never runs because block execution stops at the
    selected-case exception. -/
theorem exec_nativeSwitchCaseIfs_find_hit_with_default_error_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt) (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 9) (.Block
      (nativeSwitchCaseIfs discrName matchedName cases ++ nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .error err := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .error err :=
    exec_nativeSwitchCaseIfs_find_hit_error_fuel fuel selector cases tag body
      codeOverride state discrName matchedName err hFind hMatched
      hDiscrSelector hSelectorRange hTagsRange hBody
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using
      (exec_block_append_prefix_error fuel 9
        (nativeSwitchCaseIfs discrName matchedName cases)
        (nativeSwitchDefaultIf matchedName defaultBody)
        codeOverride state err
        (by simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hCases))

/-- Selector-miss execution for the generated case chain followed by a
    non-empty generated default block. -/
theorem exec_nativeSwitchCaseIfs_find_none_with_default_nonempty_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = none)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size)
    (hDefaultBody :
      EvmYul.Yul.exec (fuel + 7) (.Block defaultBody) codeOverride state =
        .ok final)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok final := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .ok state :=
    exec_nativeSwitchCaseIfs_find_none_fuel fuel selector cases codeOverride
      state discrName matchedName hFind hMatched hDiscrSelector hSelectorRange
      hTagsRange
  have hDefault :
      EvmYul.Yul.exec (fuel + 9)
        (.Block (nativeSwitchDefaultIf matchedName defaultBody))
        codeOverride state = .ok final :=
    exec_nativeSwitchDefaultIf_unmatched_caseTail_nonempty_fuel fuel
      defaultBody codeOverride state final matchedName hMatched hDefaultBody
      hNonempty
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using
      (exec_block_append_ok fuel 9
        (nativeSwitchCaseIfs discrName matchedName cases)
        (nativeSwitchDefaultIf matchedName defaultBody)
        codeOverride state state final
        (by simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hCases)
        hDefault)

/-- Selector-miss execution for the generated case chain followed by a
    non-empty generated default block that halts or errors. -/
theorem exec_nativeSwitchCaseIfs_find_none_with_default_nonempty_error_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size)
    (hDefaultBody :
      EvmYul.Yul.exec (fuel + 7) (.Block defaultBody) codeOverride state =
        .error err)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .error err := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9) (.Block
        (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .ok state :=
    exec_nativeSwitchCaseIfs_find_none_fuel fuel selector cases codeOverride
      state discrName matchedName hFind hMatched hDiscrSelector hSelectorRange
      hTagsRange
  have hDefault :
      EvmYul.Yul.exec (fuel + 9) (.Block
        (nativeSwitchDefaultIf matchedName defaultBody))
        codeOverride state = .error err :=
    exec_nativeSwitchDefaultIf_unmatched_caseTail_nonempty_error_fuel fuel
      defaultBody codeOverride state matchedName err hMatched hDefaultBody
      hNonempty
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using
      (exec_block_append_error fuel 9
        (nativeSwitchCaseIfs discrName matchedName cases)
        (nativeSwitchDefaultIf matchedName defaultBody)
        codeOverride state state err
        (by simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hCases)
        hDefault)

/-- Guarded selector-miss execution for the generated lazy switch when the
    default body is the compiler's `revert(0, 0)` statement. This discharges the
    default-body premise in the generic selector-miss theorem with the actual
    native `REVERT` primitive path. -/
theorem exec_nativeSwitchCaseIfs_find_none_with_revert_default_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = none)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName [nativeRevertZeroZeroStmt]))
      codeOverride state = .error EvmYul.Yul.Exception.Revert := by
  have hDefaultBody :
      EvmYul.Yul.exec (fuel + 7) (.Block [nativeRevertZeroZeroStmt])
        codeOverride state = .error EvmYul.Yul.Exception.Revert := by
    exact exec_block_cons_error (fuel + 6) nativeRevertZeroZeroStmt []
      codeOverride state EvmYul.Yul.Exception.Revert
      (exec_revert_zero_zero_error fuel state codeOverride)
  exact exec_nativeSwitchCaseIfs_find_none_with_default_nonempty_error_fuel
    fuel selector cases [nativeRevertZeroZeroStmt] codeOverride state
    discrName matchedName EvmYul.Yul.Exception.Revert hFind hMatched
    hDiscrSelector hSelectorRange hTagsRange hDefaultBody (by simp)

/-- Selector-miss execution for the generated case chain when no default is
    emitted. -/
theorem exec_nativeSwitchCaseIfs_find_none_without_default_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = none)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName []))
      codeOverride state = .ok state := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .ok state :=
    exec_nativeSwitchCaseIfs_find_none_fuel fuel selector cases codeOverride
      state discrName matchedName hFind hMatched hDiscrSelector hSelectorRange
      hTagsRange
  have hDefault :
      EvmYul.Yul.exec (fuel + 9)
        (.Block (nativeSwitchDefaultIf matchedName []))
        codeOverride state = .ok state := by
    simp [nativeSwitchDefaultIf, EvmYul.Yul.exec]
  simpa [nativeSwitchCaseIfs, nativeSwitchDefaultIf, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
      (exec_block_append_ok fuel 9
        (nativeSwitchCaseIfs discrName matchedName cases)
        (nativeSwitchDefaultIf matchedName [])
        codeOverride state state state
        (by simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hCases)
        hDefault)

theorem exec_nativeSwitchPrefix_then_tail_fuel
    (fuel : Nat)
    (tail : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier)
    (final : EvmYul.Yul.State)
    (hTail :
      EvmYul.Yul.exec (fuel + 10) (.Block tail) (some contract)
        (nativeSwitchPrefixFinalState contract tx storage observableSlots
          discrName matchedName) =
        .ok final) :
    EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName ++ tail))
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok final := by
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hPrefix :
      EvmYul.Yul.exec (fuel + 12)
        (.Block (nativeSwitchPrefixStmts discrName matchedName))
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .ok prefixState := by
    simpa [prefixState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (exec_nativeSwitchPrefix_selector_initialState_ok_fuel fuel
        contract tx storage observableSlots discrName matchedName)
  exact exec_block_append_ok (fuel + 10) 0
    (nativeSwitchPrefixStmts discrName matchedName) tail
    (some contract)
    (nativeSwitchInitialOkState contract tx storage observableSlots)
    prefixState final
    (by simpa [nativeSwitchPrefixStmts, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hPrefix)
    (by simpa [prefixState] using hTail)

theorem exec_nativeSwitchPrefix_then_tail_error_fuel
    (fuel : Nat)
    (tail : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hTail :
      EvmYul.Yul.exec (fuel + 10) (.Block tail) (some contract)
        (nativeSwitchPrefixFinalState contract tx storage observableSlots
          discrName matchedName) =
        .error err) :
    EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName ++ tail))
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .error err := by
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hPrefix :
      EvmYul.Yul.exec (fuel + 12)
        (.Block (nativeSwitchPrefixStmts discrName matchedName))
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .ok prefixState := by
    simpa [prefixState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (exec_nativeSwitchPrefix_selector_initialState_ok_fuel fuel
        contract tx storage observableSlots discrName matchedName)
  exact exec_block_append_error (fuel + 10) 0
    (nativeSwitchPrefixStmts discrName matchedName) tail
    (some contract)
    (nativeSwitchInitialOkState contract tx storage observableSlots)
    prefixState err
    (by simpa [nativeSwitchPrefixStmts, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hPrefix)
    (by simpa [prefixState] using hTail)

theorem exec_nativeSwitchTail_find_hit_preserved_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt)) (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchMarkedPrefixStateForId contract tx storage observableSlots switchId) = .ok final)
    (hPreservesMatched : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1) body (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases defaultBody))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage observableSlots switchId) =
    .ok final := by
  let discrName : EvmYul.Identifier := Backends.nativeSwitchDiscrTempName switchId
  let matchedName : EvmYul.Identifier := Backends.nativeSwitchMatchedTempName switchId
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hCasesDefault :=
    exec_nativeSwitchCaseIfs_find_hit_with_default_preserved_fuel
      (fuel + 1) selector cases defaultBody tag body (some contract)
      prefixState final discrName matchedName hFind
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_matched contract tx storage
          observableSlots discrName matchedName))
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_discr contract tx storage observableSlots
          discrName matchedName selector
          (nativeSwitchDiscrTempName_ne_matchedTempName switchId) hSelector))
      hSelectorRange hTagsRange
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_marked contract tx storage
          observableSlots discrName matchedName))
      (by intro pre suffix hCases; simpa [nativeSwitchMarkedPrefixStateForId,
        nativeSwitchPrefixStateForId, prefixState, discrName, matchedName]
        using hBody pre suffix hCases)
      (by intro pre suffix hCases; simpa [matchedName] using
        hPreservesMatched pre suffix hCases)
  simpa [nativeSwitchTailStmts, nativeSwitchPrefixStateForId, prefixState,
    discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hCasesDefault

/-- Selector-hit switch-tail execution deriving matched-flag preservation from generated freshness. -/
theorem exec_nativeSwitchTail_find_hit_fresh_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt)) (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchMarkedPrefixStateForId contract tx storage observableSlots switchId) = .ok final)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases defaultBody))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage observableSlots switchId) =
    .ok final := by
  apply exec_nativeSwitchTail_find_hit_preserved_fuel fuel selector switchId tag
    cases defaultBody body contract tx storage observableSlots final hSelector
    hFind hSelectorRange hTagsRange hBody
  intro pre suffix _hCases
  exact NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_matched
    switchId selector tag body defaultBody cases (EvmYul.UInt256.ofNat 1)
    (some contract) hFresh hFind hStmtPreserves

theorem exec_nativeSwitchTail_find_hit_error_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchMarkedPrefixStateForId contract tx storage observableSlots switchId) = .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases defaultBody))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage observableSlots switchId) =
    .error err := by
  let discrName : EvmYul.Identifier := Backends.nativeSwitchDiscrTempName switchId
  let matchedName : EvmYul.Identifier := Backends.nativeSwitchMatchedTempName switchId
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hCasesDefault :=
    exec_nativeSwitchCaseIfs_find_hit_with_default_error_fuel
      (fuel + 1) selector cases defaultBody tag body (some contract)
      prefixState discrName matchedName err hFind
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_matched contract tx storage
          observableSlots discrName matchedName))
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_discr contract tx storage observableSlots
          discrName matchedName selector
          (nativeSwitchDiscrTempName_ne_matchedTempName switchId) hSelector))
      hSelectorRange hTagsRange
      (by intro pre suffix hCases; simpa [nativeSwitchMarkedPrefixStateForId,
        nativeSwitchPrefixStateForId, prefixState, discrName, matchedName]
        using hBody pre suffix hCases)
  simpa [nativeSwitchTailStmts, nativeSwitchPrefixStateForId, prefixState,
    discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hCasesDefault

theorem exec_nativeSwitchTail_find_none_with_default_nonempty_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size)
    (hDefaultBody :
      EvmYul.Yul.exec ((fuel + 1) + 7) (.Block defaultBody) (some contract)
        (nativeSwitchPrefixStateForId contract tx storage observableSlots
          switchId) = .ok final)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases defaultBody))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage
        observableSlots switchId) =
    .ok final := by
  let discrName : EvmYul.Identifier := Backends.nativeSwitchDiscrTempName switchId
  let matchedName : EvmYul.Identifier := Backends.nativeSwitchMatchedTempName switchId
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hCasesDefault :=
    exec_nativeSwitchCaseIfs_find_none_with_default_nonempty_fuel
      (fuel + 1) selector cases defaultBody (some contract)
      prefixState final discrName matchedName hFind
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_matched contract tx storage
          observableSlots discrName matchedName))
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_discr contract tx storage observableSlots
          discrName matchedName selector
          (nativeSwitchDiscrTempName_ne_matchedTempName switchId) hSelector))
      hSelectorRange hTagsRange
      (by simpa [nativeSwitchPrefixStateForId, prefixState, discrName,
        matchedName] using hDefaultBody)
      hNonempty
  simpa [nativeSwitchTailStmts, nativeSwitchPrefixStateForId, prefixState,
    discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hCasesDefault

theorem exec_nativeSwitchTail_find_none_without_default_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases []))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage
        observableSlots switchId) =
    .ok (nativeSwitchPrefixStateForId contract tx storage observableSlots
      switchId) := by
  let discrName : EvmYul.Identifier := Backends.nativeSwitchDiscrTempName switchId
  let matchedName : EvmYul.Identifier := Backends.nativeSwitchMatchedTempName switchId
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hCasesDefault :=
    exec_nativeSwitchCaseIfs_find_none_without_default_fuel
      (fuel + 1) selector cases (some contract)
      prefixState discrName matchedName hFind
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_matched contract tx storage
          observableSlots discrName matchedName))
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_discr contract tx storage observableSlots
          discrName matchedName selector
          (nativeSwitchDiscrTempName_ne_matchedTempName switchId) hSelector))
      hSelectorRange hTagsRange
  simpa [nativeSwitchTailStmts, nativeSwitchPrefixStateForId, prefixState,
    discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hCasesDefault

/-- Selector-miss execution for a lowered switch tail with the compiler's
    generated `revert(0, 0)` default. This carries the guarded miss proof from
    the case-chain level to the switch-tail shape used by lowered dispatchers. -/
theorem exec_nativeSwitchTail_find_none_with_revert_default_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases [nativeRevertZeroZeroStmt]))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage
        observableSlots switchId) =
    .error EvmYul.Yul.Exception.Revert := by
  let discrName : EvmYul.Identifier := Backends.nativeSwitchDiscrTempName switchId
  let matchedName : EvmYul.Identifier := Backends.nativeSwitchMatchedTempName switchId
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hCasesDefault :=
    exec_nativeSwitchCaseIfs_find_none_with_revert_default_fuel
      (fuel + 1) selector cases (some contract)
      prefixState discrName matchedName hFind
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_matched contract tx storage
          observableSlots discrName matchedName))
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_discr contract tx storage observableSlots
          discrName matchedName selector
          (nativeSwitchDiscrTempName_ne_matchedTempName switchId) hSelector))
      hSelectorRange hTagsRange
  simpa [nativeSwitchTailStmts, nativeSwitchPrefixStateForId, prefixState,
    discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hCasesDefault

theorem exec_lowerNativeSwitchBlock_selector_find_hit_preserved_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((nativeSwitchPrefixFinalState contract tx storage observableSlots
          (Backends.nativeSwitchDiscrTempName switchId)
          (Backends.nativeSwitchMatchedTempName switchId)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) = .ok final)
    (hPreservesMatched : ∀ pre suffix,
      cases = pre ++ (tag, body) :: suffix →
        NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          (EvmYul.UInt256.ofNat 1) body (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok final := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_fuel
  exact exec_nativeSwitchTail_find_hit_preserved_fuel fuel selector switchId tag
    cases defaultBody body contract tx storage observableSlots final
    hSelector hFind hSelectorRange hTagsRange hBody hPreservesMatched

theorem exec_lowerNativeSwitchBlock_selector_find_hit_fresh_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((nativeSwitchPrefixFinalState contract tx storage observableSlots
          (Backends.nativeSwitchDiscrTempName switchId)
          (Backends.nativeSwitchMatchedTempName switchId)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) = .ok final)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok final := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_fuel
  exact exec_nativeSwitchTail_find_hit_fresh_fuel fuel selector switchId tag
    cases defaultBody body contract tx storage observableSlots final hSelector
    hFind hSelectorRange hTagsRange hFresh hBody hStmtPreserves

theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((nativeSwitchPrefixFinalState contract tx storage observableSlots
          (Backends.nativeSwitchDiscrTempName switchId)
          (Backends.nativeSwitchMatchedTempName switchId)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .error err := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_error_fuel
  exact exec_nativeSwitchTail_find_hit_error_fuel fuel selector switchId tag
    cases defaultBody body contract tx storage observableSlots err
    hSelector hFind hSelectorRange hTagsRange hBody

theorem exec_lowerNativeSwitchBlock_selector_find_none_with_default_nonempty_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size)
    (hDefaultBody :
      EvmYul.Yul.exec ((fuel + 1) + 7) (.Block defaultBody) (some contract)
        (nativeSwitchPrefixFinalState contract tx storage observableSlots
          (Backends.nativeSwitchDiscrTempName switchId)
          (Backends.nativeSwitchMatchedTempName switchId)) =
        .ok final)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok final := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_fuel
  exact exec_nativeSwitchTail_find_none_with_default_nonempty_fuel fuel
    selector switchId cases defaultBody contract tx storage observableSlots
    final hSelector hFind hSelectorRange hTagsRange hDefaultBody hNonempty

/-- Guarded selector-miss execution for a fully lowered native switch block
    whose generated default is `revert(0, 0)`. This discharges the generic
    default-body premise with the actual native `REVERT` primitive path at the
    same lowered-block boundary used by dispatcher proofs. -/
theorem exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases
          [nativeRevertZeroZeroStmt])
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_error_fuel
  exact exec_nativeSwitchTail_find_none_with_revert_default_fuel fuel selector
    switchId cases contract tx storage observableSlots hSelector hFind
    hSelectorRange hTagsRange

/-- Store-parametric prefix-then-tail-error glue for `lowerNativeSwitchBlock`.
    Given the tail body errors on the post-prefix state extended over an
    arbitrary preceding native varstore, the full lowered switch block errors
    on the matching state with that store. Together with the store-parametric
    prefix lemma `exec_nativeSwitchPrefix_selector_initialState_store_ok_fuel`,
    this lifts switch-block error proofs to states already carrying additional
    bindings (e.g. the buildSwitch wrapper's `__has_selector := 1`). -/
theorem exec_lowerNativeSwitchBlock_storePrefix_tail_error_fuel
    (fuel switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hTail :
      EvmYul.Yul.exec (fuel + 10)
        (.Block (nativeSwitchTailStmts switchId cases defaultBody))
        (some contract)
        (((.Ok (initialState contract tx storage observableSlots).sharedState store
                : EvmYul.Yul.State).insert
              (Backends.nativeSwitchDiscrTempName switchId)
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 0)) =
        .error err) :
    EvmYul.Yul.exec (fuel + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (.Ok (initialState contract tx storage observableSlots).sharedState store) =
    .error err := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  let initState : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let prefixState : EvmYul.Yul.State :=
    (initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
      matchedName (EvmYul.UInt256.ofNat 0)
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_block_append_error (fuel + 10) 0
    (nativeSwitchPrefixStmts discrName matchedName)
    (nativeSwitchTailStmts switchId cases defaultBody)
    (some contract) initState prefixState err
  · simpa [nativeSwitchPrefixStmts, prefixState, initState, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      exec_nativeSwitchPrefix_selector_initialState_store_ok_fuel
        fuel contract tx storage observableSlots store discrName matchedName
  · simpa [prefixState, initState] using hTail

/-- Post-generated-init variant of
    `exec_lowerNativeSwitchBlock_storePrefix_tail_error_fuel`. This is the
    exact glue needed after `initFreeMemoryPointer` has updated memory and the
    generated dispatcher has already bound `__has_selector`. -/
theorem exec_lowerNativeSwitchBlock_postInitFreeMemory_storePrefix_tail_error_fuel
    (fuel switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hTail :
      EvmYul.Yul.exec (fuel + 10)
        (.Block (nativeSwitchTailStmts switchId cases defaultBody))
        (some contract)
        (((nativeSwitchPostInitFreeMemoryState contract tx storage
              observableSlots store).insert
              (Backends.nativeSwitchDiscrTempName switchId)
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 0)) =
        .error err) :
    EvmYul.Yul.exec (fuel + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchPostInitFreeMemoryState contract tx storage
        observableSlots store) =
    .error err := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  let initState : EvmYul.Yul.State :=
    nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots store
  let prefixState : EvmYul.Yul.State :=
    (initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
      matchedName (EvmYul.UInt256.ofNat 0)
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_block_append_error (fuel + 10) 0
    (nativeSwitchPrefixStmts discrName matchedName)
    (nativeSwitchTailStmts switchId cases defaultBody)
    (some contract) initState prefixState err
  · simpa [nativeSwitchPrefixStmts, prefixState, initState, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      exec_nativeSwitchPrefix_selector_postInitFreeMemory_store_ok_fuel
        fuel contract tx storage observableSlots store discrName matchedName
  · simpa [prefixState, initState, discrName, matchedName] using hTail

/-- Post-generated-init prefix-then-tail-success glue for
    `lowerNativeSwitchBlock`. This is the success companion to
    `exec_lowerNativeSwitchBlock_postInitFreeMemory_storePrefix_tail_error_fuel`. -/
theorem exec_lowerNativeSwitchBlock_postInitFreeMemory_storePrefix_tail_ok_fuel
    (fuel switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (hTail :
      EvmYul.Yul.exec (fuel + 10)
        (.Block (nativeSwitchTailStmts switchId cases defaultBody))
        (some contract)
        (((nativeSwitchPostInitFreeMemoryState contract tx storage
              observableSlots store).insert
              (Backends.nativeSwitchDiscrTempName switchId)
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 0)) =
        .ok final) :
    EvmYul.Yul.exec (fuel + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchPostInitFreeMemoryState contract tx storage
        observableSlots store) =
    .ok final := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  let initState : EvmYul.Yul.State :=
    nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots store
  let prefixState : EvmYul.Yul.State :=
    (initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
      matchedName (EvmYul.UInt256.ofNat 0)
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_block_append_ok (fuel + 10) 0
    (nativeSwitchPrefixStmts discrName matchedName)
    (nativeSwitchTailStmts switchId cases defaultBody)
    (some contract) initState prefixState final
  · simpa [nativeSwitchPrefixStmts, prefixState, initState, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      exec_nativeSwitchPrefix_selector_postInitFreeMemory_store_ok_fuel
        fuel contract tx storage observableSlots store discrName matchedName
  · simpa [prefixState, initState, discrName, matchedName] using hTail

def nativeSwitchStoreInitialState
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore) : EvmYul.Yul.State :=
  .Ok (initialState contract tx storage observableSlots).sharedState store

def nativeSwitchStorePrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) : EvmYul.Yul.State :=
  ((nativeSwitchStoreInitialState contract tx storage observableSlots store).insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
    (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 0)

def nativeSwitchStoreMarkedPrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) : EvmYul.Yul.State :=
  (nativeSwitchStorePrefixStateForId contract tx storage observableSlots
    switchId store).insert
    (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 1)

def nativeSwitchPostInitFreeMemoryStorePrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) : EvmYul.Yul.State :=
  ((nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
      store).insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
    (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 0)

def nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) : EvmYul.Yul.State :=
  (nativeSwitchPostInitFreeMemoryStorePrefixStateForId contract tx storage
    observableSlots switchId store).insert
    (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 1)

theorem nativeSwitchStoreMarkedPrefixStateForId_reviveJump_eq
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) :
    (nativeSwitchStoreMarkedPrefixStateForId contract tx storage observableSlots
      switchId store).reviveJump =
      nativeSwitchStoreMarkedPrefixStateForId contract tx storage observableSlots
        switchId store := by
  simp [nativeSwitchStoreMarkedPrefixStateForId,
    nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.reviveJump]

theorem nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId_reviveJump_eq
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) :
    (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
      storage observableSlots switchId store).reviveJump =
      nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
        storage observableSlots switchId store := by
  simp [nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
    nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
    nativeSwitchPostInitFreeMemoryState,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.reviveJump]

@[simp] theorem nativeSwitchStoreMarkedPrefixStateForId_weiValue
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) :
    (nativeSwitchStoreMarkedPrefixStateForId contract tx storage observableSlots
      switchId store).sharedState.executionEnv.weiValue =
      natToUInt256 tx.msgValue := by
  simp [nativeSwitchStoreMarkedPrefixStateForId,
    nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
    initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.insert,
    YulState.initial, toSharedState, mkBlockHeader]

@[simp] theorem nativeSwitchStoreMarkedPrefixStateForId_calldata_size
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) :
    (nativeSwitchStoreMarkedPrefixStateForId contract tx storage observableSlots
      switchId store).sharedState.executionEnv.calldata.size =
      4 + tx.args.length * 32 := by
  simp [nativeSwitchStoreMarkedPrefixStateForId,
    nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
    initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.insert,
    YulState.initial, toSharedState, mkBlockHeader, calldataToByteArray_size]

@[simp] theorem nativeSwitchStoreMarkedPrefixStateForId_matched
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) :
    ∀ matchedName : EvmYul.Identifier,
      matchedName = Backends.nativeSwitchMatchedTempName switchId →
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store)[matchedName]! =
          EvmYul.UInt256.ofNat 1 := by
  intro matchedName hMatchedName
  subst matchedName
  simpa [nativeSwitchStoreMarkedPrefixStateForId,
    nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState] using
    state_getElem_insert_self_ok
      (initialState contract tx storage observableSlots).sharedState
      ((store.insert (Backends.nativeSwitchDiscrTempName switchId)
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0))
      (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 1)

@[simp] theorem nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId_weiValue
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) :
    (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
      storage observableSlots switchId store).sharedState.executionEnv.weiValue =
      natToUInt256 tx.msgValue := by
  simp [nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
    nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
    nativeSwitchPostInitFreeMemoryState,
    nativeSwitchPostInitFreeMemorySharedState, initialState,
    EvmYul.Yul.State.sharedState, EvmYul.Yul.State.insert, YulState.initial,
    toSharedState, mkBlockHeader]

@[simp] theorem nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId_calldata_size
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) :
    (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
      storage observableSlots switchId store).sharedState.executionEnv.calldata.size =
      4 + tx.args.length * 32 := by
  simp [nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
    nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
    nativeSwitchPostInitFreeMemoryState,
    nativeSwitchPostInitFreeMemorySharedState, initialState,
    EvmYul.Yul.State.sharedState, EvmYul.Yul.State.insert, YulState.initial,
    toSharedState, mkBlockHeader, calldataToByteArray_size]

@[simp] theorem nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId_matched
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) :
    ∀ matchedName : EvmYul.Identifier,
      matchedName = Backends.nativeSwitchMatchedTempName switchId →
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store)[matchedName]! =
          EvmYul.UInt256.ofNat 1 := by
  intro matchedName hMatchedName
  subst matchedName
  simpa [nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
    nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
    nativeSwitchPostInitFreeMemoryState] using
    state_getElem_insert_self_ok
      (nativeSwitchPostInitFreeMemorySharedState contract tx storage
        observableSlots)
      ((store.insert (Backends.nativeSwitchDiscrTempName switchId)
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0))
      (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 1)

/-- Selected-switch-state form of the callvalue guard skip: after the lazy
switch has selected a function case and marked the matched flag, a modular-zero
`msgValue` still skips the generated native callvalue revert guard. -/
theorem exec_if_callvalue_skip_markedPrefix_zero_mod_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (hZero : tx.msgValue % evmModulus = 0) :
    EvmYul.Yul.exec (fuel + 6)
        (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" [])) body)
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) =
      .ok (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) := by
  have hWei :
      (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
        observableSlots switchId store).sharedState.executionEnv.weiValue =
        (⟨0⟩ : EvmYul.Literal) := by
    rw [nativeSwitchStoreMarkedPrefixStateForId_weiValue]
    exact natToUInt256_eq_zero_of_mod_evm tx.msgValue hZero
  simpa [nativeSwitchStoreMarkedPrefixStateForId,
    nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
    EvmYul.Yul.State.insert] using
    exec_if_lowerExprNative_callvalue_skip_zero_fuel fuel body (some contract)
      (initialState contract tx storage observableSlots).sharedState
      (((store.insert (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
          (Backends.nativeSwitchMatchedTempName switchId)
          (EvmYul.UInt256.ofNat 0)).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1))
      hWei

/-- Selected-switch-state form of the callvalue guard failure: after the lazy
switch has selected a non-payable function case and the transaction has
nonzero modular `msgValue`, the generated native `callvalue()` guard executes
its `revert(0, 0)` body and returns a native revert error. -/
theorem exec_if_callvalue_take_markedPrefix_nonzero_revert_fuel
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (hNonzero : tx.msgValue % evmModulus ≠ 0) :
    EvmYul.Yul.exec (fuel + 8)
        (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) =
      .error EvmYul.Yul.Exception.Revert := by
  let state :=
    nativeSwitchStoreMarkedPrefixStateForId contract tx storage
      observableSlots switchId store
  have hEval :
      EvmYul.Yul.eval (fuel + 7)
          (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
          (some contract) state =
        .ok (state, natToUInt256 tx.msgValue) := by
    simpa [state] using
      (eval_lowerExprNative_callvalue_ok_fuel (fuel + 2)
        (state.sharedState) (state.store) (some contract))
  have hBody :
      EvmYul.Yul.exec (fuel + 7) (.Block [nativeRevertZeroZeroStmt])
          (some contract) state =
        .error EvmYul.Yul.Exception.Revert := by
    have hFuel : fuel + 7 = Nat.succ (fuel + 6) := by omega
    rw [hFuel]
    exact exec_block_cons_error (fuel + 6) nativeRevertZeroZeroStmt []
      (some contract) state EvmYul.Yul.Exception.Revert
      (exec_revert_zero_zero_error fuel state (some contract))
  have hFuel : fuel + 8 = Nat.succ (fuel + 7) := by omega
  rw [hFuel]
  exact exec_if_eval_nonzero_error (fuel + 7)
    (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
    [nativeRevertZeroZeroStmt] (some contract) state state
    (natToUInt256 tx.msgValue) EvmYul.Yul.Exception.Revert
    hEval (natToUInt256_ne_zero_of_mod_ne tx.msgValue hNonzero) hBody

/-- Selected-switch-state form of the calldata-size guard skip: after the lazy
switch has selected a function case and marked the matched flag, the generated
`lt(calldatasize(), k)` revert guard skips whenever the current calldata size
is at least `k`. -/
theorem exec_if_lt_calldatasize_skip_markedPrefix_ge_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hSize : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hGe : k ≤ 4 + tx.args.length * 32) :
    EvmYul.Yul.exec (fuel + 9)
        (.If (Backends.lowerExprNative
                (Yul.YulExpr.call "lt"
                  [Yul.YulExpr.call "calldatasize" [],
                   Yul.YulExpr.lit k]))
          body)
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) =
      .ok (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) := by
  have hSize' :
      (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
        observableSlots switchId store).sharedState.executionEnv.calldata.size <
        EvmYul.UInt256.size := by
    simpa using hSize
  have hGe' :
      k ≤
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store).sharedState.executionEnv.calldata.size := by
    simpa using hGe
  simpa [nativeSwitchStoreMarkedPrefixStateForId,
    nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
    EvmYul.Yul.State.insert] using
    exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel fuel body
      (some contract)
      (initialState contract tx storage observableSlots).sharedState
      (((store.insert (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
          (Backends.nativeSwitchMatchedTempName switchId)
          (EvmYul.UInt256.ofNat 0)).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1))
      k hSize' hKSize hGe'

/-- Selected-switch-state form of the calldata-size guard take: after the lazy
switch has selected a function case and marked the matched flag, the generated
`lt(calldatasize(), k)` revert guard executes `revert(0, 0)` whenever the
current calldata size is less than `k`. -/
theorem exec_if_lt_calldatasize_take_markedPrefix_lt_revert_fuel
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hSize : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hLt : 4 + tx.args.length * 32 < k) :
    EvmYul.Yul.exec (fuel + 9)
        (.If (Backends.lowerExprNative
                (Yul.YulExpr.call "lt"
                  [Yul.YulExpr.call "calldatasize" [],
                   Yul.YulExpr.lit k]))
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) =
      .error EvmYul.Yul.Exception.Revert := by
  have hSize' :
      (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
        observableSlots switchId store).sharedState.executionEnv.calldata.size <
        EvmYul.UInt256.size := by
    simpa using hSize
  have hLt' :
      (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
        observableSlots switchId store).sharedState.executionEnv.calldata.size <
        k := by
    simpa using hLt
  simpa [nativeSwitchStoreMarkedPrefixStateForId,
    nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
    EvmYul.Yul.State.insert] using
    exec_if_lowerExprNative_lt_calldatasize_take_lt_revert_fuel fuel
      (some contract)
      (initialState contract tx storage observableSlots).sharedState
      (((store.insert (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
          (Backends.nativeSwitchMatchedTempName switchId)
          (EvmYul.UInt256.ofNat 0)).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1))
      k hSize' hKSize hLt'

/-- Execute a payable selected switch-case prefix as a no-op and continue with
the lowered user body. The generated case prefix is the lowered comment no-op
followed by the calldata-size revert guard. -/
theorem exec_switchCaseBody_payable_prefix_eq
    (fuel : Nat)
    (guardBody bodyNative : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hSize : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hGe : k ≤ 4 + tx.args.length * 32) :
    EvmYul.Yul.exec (fuel + 11)
        (.Block
          (EvmYul.Yul.Ast.Stmt.Block [] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            guardBody ::
           bodyNative))
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) =
      EvmYul.Yul.exec (fuel + 9) (.Block bodyNative)
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) := by
  have hFuel : fuel + 11 = Nat.succ (Nat.succ (fuel + 9)) := by omega
  rw [hFuel]
  rw [exec_block_noop_block_head_eq]
  apply exec_block_cons_ok_eq (fuel + 9)
  exact exec_if_lt_calldatasize_skip_markedPrefix_ge_fuel fuel guardBody
    contract tx storage observableSlots switchId store k hSize hKSize hGe

/-- Post-generated-init variant of `exec_switchCaseBody_payable_prefix_eq`. -/
theorem exec_switchCaseBody_payable_prefix_postInitFreeMemory_eq
    (fuel : Nat)
    (guardBody bodyNative : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hSize : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hGe : k ≤ 4 + tx.args.length * 32) :
    EvmYul.Yul.exec (fuel + 11)
        (.Block
          (EvmYul.Yul.Ast.Stmt.Block [] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            guardBody ::
           bodyNative))
        (some contract)
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) =
      EvmYul.Yul.exec (fuel + 9) (.Block bodyNative)
        (some contract)
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) := by
  let state :=
    nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
      storage observableSlots switchId store
  have hSize' : state.sharedState.executionEnv.calldata.size <
      EvmYul.UInt256.size := by
    simpa [state] using hSize
  have hGe' : k ≤ state.sharedState.executionEnv.calldata.size := by
    simpa [state] using hGe
  have hGuard :
      EvmYul.Yul.exec (fuel + 9)
        (.If (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
          guardBody)
        (some contract) state =
      .ok state :=
    exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel fuel guardBody
      (some contract) state.sharedState state.store k hSize' hKSize hGe'
  have hFuel : fuel + 11 = Nat.succ (Nat.succ (fuel + 9)) := by omega
  rw [hFuel]
  rw [exec_block_noop_block_head_eq]
  simpa [state] using
    exec_block_cons_ok_eq (fuel + 9)
      (EvmYul.Yul.Ast.Stmt.If
        (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
        guardBody)
      bodyNative (some contract) state state hGuard

/-- Execute a payable selected switch-case prefix through the failing
calldata-size guard. The generated label no-op is skipped, then the concrete
`lt(calldatasize(), k)` guard runs its `revert(0, 0)` body before any user
body statements execute. -/
theorem exec_switchCaseBody_payable_calldata_revert_fuel
    (fuel : Nat)
    (bodyNative : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hSize : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hLt : 4 + tx.args.length * 32 < k) :
    EvmYul.Yul.exec (fuel + 11)
        (.Block
          (EvmYul.Yul.Ast.Stmt.Block [] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            [nativeRevertZeroZeroStmt] ::
           bodyNative))
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) =
      .error EvmYul.Yul.Exception.Revert := by
  have hFuel : fuel + 11 = Nat.succ (Nat.succ (fuel + 9)) := by omega
  rw [hFuel]
  rw [exec_block_noop_block_head_eq]
  apply exec_block_cons_error (fuel + 9)
  exact exec_if_lt_calldatasize_take_markedPrefix_lt_revert_fuel fuel
    contract tx storage observableSlots switchId store k hSize hKSize hLt

/-- Post-generated-init variant of
    `exec_switchCaseBody_payable_calldata_revert_fuel`. -/
theorem exec_switchCaseBody_payable_calldata_revert_postInitFreeMemory_fuel
    (fuel : Nat)
    (bodyNative : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hSize : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hLt : 4 + tx.args.length * 32 < k) :
    EvmYul.Yul.exec (fuel + 11)
        (.Block
          (EvmYul.Yul.Ast.Stmt.Block [] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            [nativeRevertZeroZeroStmt] ::
           bodyNative))
        (some contract)
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) =
      .error EvmYul.Yul.Exception.Revert := by
  let state :=
    nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
      storage observableSlots switchId store
  have hSize' : state.sharedState.executionEnv.calldata.size <
      EvmYul.UInt256.size := by
    simpa [state] using hSize
  have hLt' : state.sharedState.executionEnv.calldata.size < k := by
    simpa [state] using hLt
  have hGuard :
      EvmYul.Yul.exec (fuel + 9)
        (.If (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
          [nativeRevertZeroZeroStmt])
        (some contract) state =
      .error EvmYul.Yul.Exception.Revert :=
    exec_if_lowerExprNative_lt_calldatasize_take_lt_revert_fuel fuel
      (some contract) state.sharedState state.store k hSize' hKSize hLt'
  have hFuel : fuel + 11 = Nat.succ (Nat.succ (fuel + 9)) := by omega
  rw [hFuel]
  rw [exec_block_noop_block_head_eq]
  simpa [state] using
    exec_block_cons_error (fuel + 9)
      (EvmYul.Yul.Ast.Stmt.If
        (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
        [nativeRevertZeroZeroStmt])
      bodyNative (some contract) state EvmYul.Yul.Exception.Revert hGuard

/-- Execute a non-payable selected switch-case prefix as no-ops and continue
with the lowered user body. The generated case prefix is the lowered comment
no-op, the callvalue revert guard, and then the calldata-size revert guard. -/
theorem exec_switchCaseBody_nonpayable_prefix_eq
    (fuel : Nat)
    (callvalueGuardBody calldataGuardBody bodyNative :
      List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hZero : tx.msgValue % evmModulus = 0)
    (hSize : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hGe : k ≤ 4 + tx.args.length * 32) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block
          (EvmYul.Yul.Ast.Stmt.Block [] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            callvalueGuardBody ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            calldataGuardBody ::
           bodyNative))
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) =
      EvmYul.Yul.exec (fuel + 9) (.Block bodyNative)
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) := by
  have hFuel : fuel + 12 = Nat.succ (Nat.succ (fuel + 10)) := by omega
  rw [hFuel]
  rw [exec_block_noop_block_head_eq]
  calc
    EvmYul.Yul.exec (Nat.succ (fuel + 10))
        (.Block
          (EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            callvalueGuardBody ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            calldataGuardBody ::
           bodyNative))
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store)
        =
      EvmYul.Yul.exec (fuel + 10)
        (.Block
          (EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            calldataGuardBody ::
           bodyNative))
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) := by
          apply exec_block_cons_ok_eq (fuel + 10)
          exact exec_if_callvalue_skip_markedPrefix_zero_mod_fuel (fuel + 4)
            callvalueGuardBody contract tx storage observableSlots switchId
            store hZero
    _ = EvmYul.Yul.exec (fuel + 9) (.Block bodyNative)
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) := by
          have hTailFuel : fuel + 10 = Nat.succ (fuel + 9) := by omega
          rw [hTailFuel]
          apply exec_block_cons_ok_eq (fuel + 9)
          exact exec_if_lt_calldatasize_skip_markedPrefix_ge_fuel fuel
            calldataGuardBody contract tx storage observableSlots switchId
            store k hSize hKSize hGe

/-- Post-generated-init variant of
    `exec_switchCaseBody_nonpayable_prefix_eq`. -/
theorem exec_switchCaseBody_nonpayable_prefix_postInitFreeMemory_eq
    (fuel : Nat)
    (callvalueGuardBody calldataGuardBody bodyNative :
      List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hZero : tx.msgValue % evmModulus = 0)
    (hSize : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hGe : k ≤ 4 + tx.args.length * 32) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block
          (EvmYul.Yul.Ast.Stmt.Block [] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            callvalueGuardBody ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            calldataGuardBody ::
           bodyNative))
        (some contract)
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) =
      EvmYul.Yul.exec (fuel + 9) (.Block bodyNative)
        (some contract)
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) := by
  let state :=
    nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
      storage observableSlots switchId store
  have hWei : state.sharedState.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal) := by
    simpa [state] using natToUInt256_eq_zero_of_mod_evm tx.msgValue hZero
  have hCallvalue :
      EvmYul.Yul.exec (fuel + 10)
        (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
          callvalueGuardBody)
        (some contract) state =
      .ok state :=
    exec_if_lowerExprNative_callvalue_skip_zero_fuel (fuel + 4)
      callvalueGuardBody (some contract) state.sharedState state.store hWei
  have hSize' : state.sharedState.executionEnv.calldata.size <
      EvmYul.UInt256.size := by
    simpa [state] using hSize
  have hGe' : k ≤ state.sharedState.executionEnv.calldata.size := by
    simpa [state] using hGe
  have hCalldata :
      EvmYul.Yul.exec (fuel + 9)
        (.If (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
          calldataGuardBody)
        (some contract) state =
      .ok state :=
    exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel fuel
      calldataGuardBody (some contract) state.sharedState state.store k hSize'
      hKSize hGe'
  have hFuel : fuel + 12 = Nat.succ (Nat.succ (fuel + 10)) := by omega
  rw [hFuel]
  rw [exec_block_noop_block_head_eq]
  calc
    EvmYul.Yul.exec (Nat.succ (fuel + 10))
        (.Block
          (EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            callvalueGuardBody ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            calldataGuardBody ::
           bodyNative))
        (some contract) state =
      EvmYul.Yul.exec (fuel + 10)
        (.Block
          (EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            calldataGuardBody ::
           bodyNative))
        (some contract) state := by
          apply exec_block_cons_ok_eq (fuel + 10)
          exact hCallvalue
    _ = EvmYul.Yul.exec (fuel + 9) (.Block bodyNative)
        (some contract) state := by
          have hTailFuel : fuel + 10 = Nat.succ (fuel + 9) := by omega
          rw [hTailFuel]
          apply exec_block_cons_ok_eq (fuel + 9)
          exact hCalldata

/-- Execute a non-payable selected switch-case prefix through the failing
callvalue guard. The generated label no-op is skipped, then the concrete
`callvalue()` guard runs its `revert(0, 0)` body before any calldata guard or
user body statements execute. -/
theorem exec_switchCaseBody_nonpayable_callvalue_revert_fuel
    (fuel : Nat)
    (calldataGuardBody bodyNative : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hNonzero : tx.msgValue % evmModulus ≠ 0) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block
          (EvmYul.Yul.Ast.Stmt.Block [] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            [nativeRevertZeroZeroStmt] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            calldataGuardBody ::
           bodyNative))
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) =
      .error EvmYul.Yul.Exception.Revert := by
  have hFuel : fuel + 12 = Nat.succ (Nat.succ (fuel + 10)) := by omega
  rw [hFuel]
  rw [exec_block_noop_block_head_eq]
  apply exec_block_cons_error (fuel + 10)
  exact exec_if_callvalue_take_markedPrefix_nonzero_revert_fuel (fuel + 2)
    contract tx storage observableSlots switchId store hNonzero

/-- Post-generated-init variant of
    `exec_switchCaseBody_nonpayable_callvalue_revert_fuel`. -/
theorem exec_switchCaseBody_nonpayable_callvalue_revert_postInitFreeMemory_fuel
    (fuel : Nat)
    (calldataGuardBody bodyNative : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hNonzero : tx.msgValue % evmModulus ≠ 0) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block
          (EvmYul.Yul.Ast.Stmt.Block [] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            [nativeRevertZeroZeroStmt] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            calldataGuardBody ::
           bodyNative))
        (some contract)
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) =
      .error EvmYul.Yul.Exception.Revert := by
  let state :=
    nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
      storage observableSlots switchId store
  have hGuard :
      EvmYul.Yul.exec (fuel + 10)
        (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
          [nativeRevertZeroZeroStmt])
        (some contract) state =
      .error EvmYul.Yul.Exception.Revert := by
    have hEval :
        EvmYul.Yul.eval (fuel + 9)
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            (some contract) state =
          .ok (state, natToUInt256 tx.msgValue) := by
      simpa [state] using
        (eval_lowerExprNative_callvalue_ok_fuel (fuel + 4)
          (state.sharedState) (state.store) (some contract))
    have hBody :
        EvmYul.Yul.exec (fuel + 9) (.Block [nativeRevertZeroZeroStmt])
            (some contract) state =
          .error EvmYul.Yul.Exception.Revert := by
      have hFuel : fuel + 9 = Nat.succ (fuel + 8) := by omega
      rw [hFuel]
      exact exec_block_cons_error (fuel + 8) nativeRevertZeroZeroStmt []
        (some contract) state EvmYul.Yul.Exception.Revert
        (exec_revert_zero_zero_error (fuel + 2) state (some contract))
    have hFuel : fuel + 10 = Nat.succ (fuel + 9) := by omega
    rw [hFuel]
    exact exec_if_eval_nonzero_error (fuel + 9)
      (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
      [nativeRevertZeroZeroStmt] (some contract) state state
      (natToUInt256 tx.msgValue) EvmYul.Yul.Exception.Revert
      hEval (natToUInt256_ne_zero_of_mod_ne tx.msgValue hNonzero) hBody
  have hFuel : fuel + 12 = Nat.succ (Nat.succ (fuel + 10)) := by omega
  rw [hFuel]
  rw [exec_block_noop_block_head_eq]
  simpa [state] using
    exec_block_cons_error (fuel + 10)
      (EvmYul.Yul.Ast.Stmt.If
        (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
        [nativeRevertZeroZeroStmt])
      (EvmYul.Yul.Ast.Stmt.If
        (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
        calldataGuardBody :: bodyNative)
      (some contract) state EvmYul.Yul.Exception.Revert hGuard

/-- Execute a non-payable selected switch-case prefix through the failing
calldata-size guard after the zero-callvalue guard skips. -/
theorem exec_switchCaseBody_nonpayable_calldata_revert_fuel
    (fuel : Nat)
    (bodyNative : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hZero : tx.msgValue % evmModulus = 0)
    (hSize : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hLt : 4 + tx.args.length * 32 < k) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block
          (EvmYul.Yul.Ast.Stmt.Block [] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            [nativeRevertZeroZeroStmt] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            [nativeRevertZeroZeroStmt] ::
           bodyNative))
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) =
      .error EvmYul.Yul.Exception.Revert := by
  have hFuel : fuel + 12 = Nat.succ (Nat.succ (fuel + 10)) := by omega
  rw [hFuel]
  rw [exec_block_noop_block_head_eq]
  calc
    EvmYul.Yul.exec (Nat.succ (fuel + 10))
        (.Block
          (EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            [nativeRevertZeroZeroStmt] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            [nativeRevertZeroZeroStmt] ::
           bodyNative))
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store)
        =
      EvmYul.Yul.exec (fuel + 10)
        (.Block
          (EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            [nativeRevertZeroZeroStmt] ::
           bodyNative))
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) := by
          apply exec_block_cons_ok_eq (fuel + 10)
          exact exec_if_callvalue_skip_markedPrefix_zero_mod_fuel (fuel + 4)
            [nativeRevertZeroZeroStmt] contract tx storage observableSlots
            switchId store hZero
    _ = .error EvmYul.Yul.Exception.Revert := by
          have hTailFuel : fuel + 10 = Nat.succ (fuel + 9) := by omega
          rw [hTailFuel]
          apply exec_block_cons_error (fuel + 9)
          exact exec_if_lt_calldatasize_take_markedPrefix_lt_revert_fuel fuel
            contract tx storage observableSlots switchId store k hSize hKSize
            hLt

/-- Post-generated-init variant of
    `exec_switchCaseBody_nonpayable_calldata_revert_fuel`. -/
theorem exec_switchCaseBody_nonpayable_calldata_revert_postInitFreeMemory_fuel
    (fuel : Nat)
    (bodyNative : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hZero : tx.msgValue % evmModulus = 0)
    (hSize : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hLt : 4 + tx.args.length * 32 < k) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block
          (EvmYul.Yul.Ast.Stmt.Block [] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            [nativeRevertZeroZeroStmt] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            [nativeRevertZeroZeroStmt] ::
           bodyNative))
        (some contract)
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) =
      .error EvmYul.Yul.Exception.Revert := by
  let state :=
    nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
      storage observableSlots switchId store
  have hWei :
      state.sharedState.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal) := by
    dsimp [state]
    rw [nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId_weiValue]
    exact natToUInt256_eq_zero_of_mod_evm tx.msgValue hZero
  have hCallvalue :
      EvmYul.Yul.exec (fuel + 10)
        (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
          [nativeRevertZeroZeroStmt])
        (some contract) state = .ok state := by
    exact exec_if_lowerExprNative_callvalue_skip_zero_fuel (fuel + 4)
      [nativeRevertZeroZeroStmt] (some contract) state.sharedState state.store
      hWei
  have hSize' : state.sharedState.executionEnv.calldata.size <
      EvmYul.UInt256.size := by
    simpa [state] using hSize
  have hLt' : state.sharedState.executionEnv.calldata.size < k := by
    simpa [state] using hLt
  have hCalldata :
      EvmYul.Yul.exec (fuel + 9)
        (.If
          (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
          [nativeRevertZeroZeroStmt])
        (some contract) state =
      .error EvmYul.Yul.Exception.Revert :=
    exec_if_lowerExprNative_lt_calldatasize_take_lt_revert_fuel fuel
      (some contract) state.sharedState state.store k hSize' hKSize hLt'
  have hFuel : fuel + 12 = Nat.succ (Nat.succ (fuel + 10)) := by omega
  rw [hFuel]
  rw [exec_block_noop_block_head_eq]
  calc
    EvmYul.Yul.exec (Nat.succ (fuel + 10))
        (.Block
          (EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            [nativeRevertZeroZeroStmt] ::
           EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            [nativeRevertZeroZeroStmt] ::
           bodyNative))
        (some contract) state =
      EvmYul.Yul.exec (fuel + 10)
        (.Block
          (EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
            [nativeRevertZeroZeroStmt] ::
           bodyNative))
        (some contract) state := by
          apply exec_block_cons_ok_eq (fuel + 10)
          exact hCallvalue
    _ = .error EvmYul.Yul.Exception.Revert := by
          have hTailFuel : fuel + 10 = Nat.succ (fuel + 9) := by omega
          rw [hTailFuel]
          apply exec_block_cons_error (fuel + 9)
          exact hCalldata

/-- Lowering-aware payable generated-case prefix peel. Starting from the actual
native lowering result of `switchCaseBody fn`, expose the lowered user body and
normalize execution of the generated comment/calldata guards to that body. -/
theorem exec_switchCaseBody_payable_lowered_prefix_eq
    (fuel : Nat)
    (reservedNames : List String) (n0 : Nat)
    (fn : IRFunction)
    (body' : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (body', next))
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) ∧
      EvmYul.Yul.exec (fuel + 11) (.Block body')
          (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots switchId store) =
        EvmYul.Yul.exec (fuel + 9) (.Block bodyNative)
          (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots switchId store) := by
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_eq
      reservedNames n0 fn body' next hPayable hLower with
    ⟨guardBody, bodyNative, bodyStart, hBodyShape, hBodyLower⟩
  refine ⟨bodyNative, bodyStart, hBodyLower, ?_⟩
  rw [hBodyShape]
  exact exec_switchCaseBody_payable_prefix_eq fuel guardBody bodyNative
    contract (YulTransaction.ofIR tx) storage observableSlots switchId store
    (4 + fn.params.length * 32)
    (by simpa [YulTransaction.ofIR_args] using hNoWrap)
    (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
    (by simp; omega)

/-- Lowering-aware non-payable generated-case prefix peel. Starting from the
actual native lowering result of `switchCaseBody fn`, expose the lowered user
body and normalize execution of the generated comment/callvalue/calldata guards
to that body. -/
theorem exec_switchCaseBody_nonpayable_lowered_prefix_eq
    (fuel : Nat)
    (reservedNames : List String) (n0 : Nat)
    (fn : IRFunction)
    (body' : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (body', next))
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) ∧
      EvmYul.Yul.exec (fuel + 12) (.Block body')
          (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots switchId store) =
        EvmYul.Yul.exec (fuel + 9) (.Block bodyNative)
          (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots switchId store) := by
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_eq
      reservedNames n0 fn body' next hNonPayable hLower with
    ⟨callvalueGuardBody, calldataGuardBody, bodyNative, bodyStart,
      hBodyShape, hBodyLower⟩
  refine ⟨bodyNative, bodyStart, hBodyLower, ?_⟩
  rw [hBodyShape]
  exact exec_switchCaseBody_nonpayable_prefix_eq fuel callvalueGuardBody
    calldataGuardBody bodyNative contract (YulTransaction.ofIR tx) storage
    observableSlots switchId store (4 + fn.params.length * 32)
    (DispatchGuardsSafe_msgValue_zero_mod_of_nonpayable fn tx hguards
      hNonPayable)
    (by simpa [YulTransaction.ofIR_args] using hNoWrap)
    (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
    (by simp; omega)

def nativeSwitchHasSelectorStore : EvmYul.Yul.VarStore :=
  (∅ : EvmYul.Yul.VarStore).insert "__has_selector" (EvmYul.UInt256.ofNat 1)

def nativeSwitchHasSelectorInitialState
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) : EvmYul.Yul.State :=
  nativeSwitchStoreInitialState contract tx storage observableSlots
    nativeSwitchHasSelectorStore

theorem nativeSwitchInitialOkState_insert_hasSelector_eq
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    (nativeSwitchInitialOkState contract tx storage observableSlots).insert
        "__has_selector" (EvmYul.UInt256.ofNat 1) =
      nativeSwitchHasSelectorInitialState contract tx storage observableSlots := by
  simp [nativeSwitchInitialOkState, nativeSwitchHasSelectorInitialState,
    nativeSwitchStoreInitialState, nativeSwitchHasSelectorStore,
    EvmYul.Yul.State.insert]

/-- `matched := 0` lookup on the post-prefix state with arbitrary store. -/
theorem nativeSwitchPrefixStoreState_matched_eq
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName matchedName : EvmYul.Identifier)
    (discrValue : EvmYul.Literal) :
    (((.Ok (initialState contract tx storage observableSlots).sharedState store
              : EvmYul.Yul.State).insert discrName discrValue).insert
        matchedName (EvmYul.UInt256.ofNat 0))[matchedName]! =
      EvmYul.UInt256.ofNat 0 := by
  simp [EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

/-- `discr := selector` lookup on the post-prefix state with arbitrary store. -/
theorem nativeSwitchPrefixStoreState_discr_eq
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName matchedName : EvmYul.Identifier)
    (selector : Nat) (hne : discrName ≠ matchedName)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus) :
    (((.Ok (initialState contract tx storage observableSlots).sharedState store
              : EvmYul.Yul.State).insert discrName
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        matchedName (EvmYul.UInt256.ofNat 0))[discrName]! =
      EvmYul.UInt256.ofNat selector := by
  rw [hSelector]
  simp [EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]
  rw [Finmap.lookup_insert_of_ne]
  · simp [Finmap.lookup_insert]
  · exact hne

/-- `matched := 0` lookup on the post-`initFreeMemoryPointer` prefix state
    with arbitrary store. -/
theorem nativeSwitchPostInitFreeMemoryPrefixStoreState_matched_eq
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName matchedName : EvmYul.Identifier)
    (discrValue : EvmYul.Literal) :
    (((nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
              store).insert discrName discrValue).insert
        matchedName (EvmYul.UInt256.ofNat 0))[matchedName]! =
      EvmYul.UInt256.ofNat 0 := by
  simpa [nativeSwitchPostInitFreeMemoryState, EvmYul.Yul.State.insert] using
    state_getElem_insert_self_ok
      (nativeSwitchPostInitFreeMemorySharedState contract tx storage
        observableSlots)
      (store.insert discrName discrValue)
      matchedName (EvmYul.UInt256.ofNat 0)

/-- `discr := selector` lookup on the post-`initFreeMemoryPointer` prefix state
    with arbitrary store. -/
theorem nativeSwitchPostInitFreeMemoryPrefixStoreState_discr_eq
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName matchedName : EvmYul.Identifier)
    (selector : Nat) (hne : discrName ≠ matchedName)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus) :
    (((nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
              store).insert discrName
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        matchedName (EvmYul.UInt256.ofNat 0))[discrName]! =
      EvmYul.UInt256.ofNat selector := by
  rw [hSelector]
  simp [nativeSwitchPostInitFreeMemoryState, EvmYul.Yul.State.insert,
    GetElem?.getElem!, decidableGetElem?, GetElem.getElem,
    EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]
  rw [Finmap.lookup_insert_of_ne]
  · simp [Finmap.lookup_insert]
  · exact hne

/-- Store-parametric prefix-then-tail-ok glue for `lowerNativeSwitchBlock`.
    This is the success dual of
    `exec_lowerNativeSwitchBlock_storePrefix_tail_error_fuel`: it lifts switch
    tail proofs to states already carrying additional bindings while preserving
    the final state returned by the tail. -/
theorem exec_lowerNativeSwitchBlock_storePrefix_tail_ok_fuel
    (fuel switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (hTail :
      EvmYul.Yul.exec (fuel + 10)
        (.Block (nativeSwitchTailStmts switchId cases defaultBody))
        (some contract)
        (nativeSwitchStorePrefixStateForId contract tx storage observableSlots
          switchId store) = .ok final) :
    EvmYul.Yul.exec (fuel + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchStoreInitialState contract tx storage observableSlots store) =
    .ok final := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  let initState :=
    nativeSwitchStoreInitialState contract tx storage observableSlots store
  let prefixState :=
    nativeSwitchStorePrefixStateForId contract tx storage observableSlots
      switchId store
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_block_append_ok (fuel + 10) 0
    (nativeSwitchPrefixStmts discrName matchedName)
    (nativeSwitchTailStmts switchId cases defaultBody)
    (some contract) initState prefixState final
  · simpa [nativeSwitchPrefixStmts, prefixState, initState, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, nativeSwitchStorePrefixStateForId,
      nativeSwitchStoreInitialState, discrName, matchedName] using
      exec_nativeSwitchPrefix_selector_initialState_store_ok_fuel
        fuel contract tx storage observableSlots store discrName matchedName
  · simpa [prefixState, initState] using hTail

/-- Store-parametric guarded selector-hit execution for the lowered switch
    block. This is the success dual of
    `exec_lowerNativeSwitchBlock_selector_find_hit_error_store_fuel`, retaining
    the matched-flag preservation premise needed to skip the generated default
    after a successful selected body. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_preserved_store_fuel
    (fuel selector switchId tag : Nat) (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt) (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (store : EvmYul.Yul.VarStore) (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx storage observableSlots switchId store) = .ok final)
    (hPreservesMatched : ∀ pre suffix,
      cases = pre ++ (tag, body) :: suffix →
        NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 1)
          body (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody) (some contract)
      (nativeSwitchStoreInitialState contract tx storage observableSlots store) =
    .ok final := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  have hne := nativeSwitchDiscrTempName_ne_matchedTempName switchId
  have hCases :=
    exec_nativeSwitchCaseIfs_find_hit_with_default_preserved_fuel
      (fuel + 1) selector cases defaultBody tag body (some contract) _
      final discrName matchedName hFind
      (nativeSwitchPrefixStoreState_matched_eq contract tx storage
        observableSlots store discrName matchedName _)
      (nativeSwitchPrefixStoreState_discr_eq contract tx storage
        observableSlots store discrName matchedName selector hne hSelector)
      hSelectorRange hTagsRange
      (by
        simp [EvmYul.Yul.State.insert, GetElem?.getElem!,
          decidableGetElem?, GetElem.getElem, EvmYul.Yul.State.store,
          EvmYul.Yul.State.lookup!])
      hBody
      (by intro pre suffix hCases; simpa [matchedName] using
        hPreservesMatched pre suffix hCases)
  exact exec_lowerNativeSwitchBlock_storePrefix_tail_ok_fuel
    (fuel + cases.length) switchId cases defaultBody contract tx storage
    observableSlots store final (by
      simpa [nativeSwitchTailStmts, discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
        nativeSwitchStoreMarkedPrefixStateForId] using hCases)

/-- Store-parametric selector-hit success when the selected body execution and
    final matched-flag fact are supplied directly. This is useful for generated
    case-body wrappers that prove the matched flag after peeling their own
    prefix rather than exposing whole-body preservation. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_finalMatched_store_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) = .ok final)
    (hFinalMatched :
      ∀ matchedName : EvmYul.Identifier,
        matchedName = Backends.nativeSwitchMatchedTempName switchId →
          final[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchStoreInitialState contract tx storage observableSlots store) =
    .ok final := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  have hne := nativeSwitchDiscrTempName_ne_matchedTempName switchId
  have hCasesOnly :
      EvmYul.Yul.exec (fuel + 1 + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        (some contract)
        (nativeSwitchStorePrefixStateForId contract tx storage
          observableSlots switchId store) = .ok final := by
    exact exec_nativeSwitchCaseIfs_find_hit_fuel
      (fuel + 1) selector cases tag body (some contract)
      (nativeSwitchStorePrefixStateForId contract tx storage observableSlots
        switchId store) final discrName matchedName hFind
      (nativeSwitchPrefixStoreState_matched_eq contract tx storage
        observableSlots store discrName matchedName _)
      (nativeSwitchPrefixStoreState_discr_eq contract tx storage
        observableSlots store discrName matchedName selector hne hSelector)
      hSelectorRange hTagsRange
      (by
        intro pre suffix hCases
        simpa [nativeSwitchStoreMarkedPrefixStateForId,
          nativeSwitchStorePrefixStateForId, discrName, matchedName,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hBody pre suffix hCases)
      (by simpa [matchedName] using hFinalMatched)
  have hCasesDefault :
      EvmYul.Yul.exec (fuel + 1 + cases.length + 9)
        (.Block
          (nativeSwitchCaseIfs discrName matchedName cases ++
            nativeSwitchDefaultIf matchedName defaultBody))
        (some contract)
        (nativeSwitchStorePrefixStateForId contract tx storage
          observableSlots switchId store) = .ok final := by
    exact exec_nativeSwitchCaseIfs_with_default_matched_fuel
      (fuel + 1) cases defaultBody (some contract)
      (nativeSwitchStorePrefixStateForId contract tx storage
        observableSlots switchId store) final discrName matchedName
      hCasesOnly
      (hFinalMatched matchedName rfl)
  exact exec_lowerNativeSwitchBlock_storePrefix_tail_ok_fuel
    (fuel + cases.length) switchId cases defaultBody contract tx storage
    observableSlots store final (by
      simpa [nativeSwitchTailStmts, discrName, matchedName, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, nativeSwitchStorePrefixStateForId,
        nativeSwitchStoreInitialState] using hCasesDefault)

/-- Store-parametric selector-hit success derived from generated native switch
    freshness. This removes the explicit matched-flag preservation premise for
    selected bodies when the generated freshness predicate proves the body does
    not write the matched temp. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_fresh_store_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) = .ok final)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchStoreInitialState contract tx storage observableSlots store) =
    .ok final := by
  apply exec_lowerNativeSwitchBlock_selector_find_hit_preserved_store_fuel
    fuel selector switchId tag cases defaultBody body contract tx storage
    observableSlots store final hSelector hFind hSelectorRange hTagsRange hBody
  intro pre suffix _hCases
  exact NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_matched
    switchId selector tag body defaultBody cases (EvmYul.UInt256.ofNat 1)
    (some contract) hFresh hFind hStmtPreserves

/-- Store-parametric guarded selector-miss execution for the lowered switch
    block whose default is `revert(0, 0)`. Lifts the empty-store version to
    states already carrying additional bindings (e.g. `__has_selector := 1`). -/
theorem exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases
          [nativeRevertZeroZeroStmt])
      (some contract)
      (.Ok (initialState contract tx storage observableSlots).sharedState store) =
    .error EvmYul.Yul.Exception.Revert := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  have hne := nativeSwitchDiscrTempName_ne_matchedTempName switchId
  have hCases :=
    exec_nativeSwitchCaseIfs_find_none_with_revert_default_fuel
      (fuel + 1) selector cases (some contract) _ discrName matchedName hFind
      (nativeSwitchPrefixStoreState_matched_eq contract tx storage observableSlots
        store discrName matchedName _)
        (nativeSwitchPrefixStoreState_discr_eq contract tx storage observableSlots
          store discrName matchedName selector hne hSelector)
        hSelectorRange hTagsRange
  exact exec_lowerNativeSwitchBlock_storePrefix_tail_error_fuel
    (fuel + cases.length) switchId cases [nativeRevertZeroZeroStmt]
    contract tx storage observableSlots store EvmYul.Yul.Exception.Revert
    (by simpa [nativeSwitchTailStmts, discrName, matchedName,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCases)

/-- Store-parametric guarded selector-hit execution for the lowered switch
    block. Hit-case dual of `_find_none_with_revert_default_store_fuel`. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_store_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((((.Ok (initialState contract tx storage observableSlots).sharedState
                store : EvmYul.Yul.State).insert
              (Backends.nativeSwitchDiscrTempName switchId)
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 0)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (.Ok (initialState contract tx storage observableSlots).sharedState store) =
    .error err := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  have hne := nativeSwitchDiscrTempName_ne_matchedTempName switchId
  have hCases :=
    exec_nativeSwitchCaseIfs_find_hit_with_default_error_fuel
      (fuel + 1) selector cases defaultBody tag body (some contract) _
      discrName matchedName err hFind
      (nativeSwitchPrefixStoreState_matched_eq contract tx storage
        observableSlots store discrName matchedName _)
      (nativeSwitchPrefixStoreState_discr_eq contract tx storage
        observableSlots store discrName matchedName selector hne hSelector)
      hSelectorRange hTagsRange hBody
  exact exec_lowerNativeSwitchBlock_storePrefix_tail_error_fuel
    (fuel + cases.length) switchId cases defaultBody contract tx storage
    observableSlots store err
    (by simpa [nativeSwitchTailStmts, discrName, matchedName,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCases)

/-- Post-generated-init selector-hit error execution for the lowered switch
    block. This is the post-`initFreeMemoryPointer` counterpart of
    `exec_lowerNativeSwitchBlock_selector_find_hit_error_store_fuel`; the
    post-init state is part of the modeled transition. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_postInitFreeMemory_store_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((((nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
                store).insert
              (Backends.nativeSwitchDiscrTempName switchId)
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 0)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
        store) =
    .error err := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  let prefixState : EvmYul.Yul.State :=
    ((nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
        store).insert discrName
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
      matchedName (EvmYul.UInt256.ofNat 0)
  have hne := nativeSwitchDiscrTempName_ne_matchedTempName switchId
  have hCases :=
    exec_nativeSwitchCaseIfs_find_hit_with_default_error_fuel
      (fuel + 1) selector cases defaultBody tag body (some contract) _
      discrName matchedName err hFind
      (by
        simpa [prefixState, discrName, matchedName] using
          nativeSwitchPostInitFreeMemoryPrefixStoreState_matched_eq
            contract tx storage observableSlots store discrName matchedName
            (EvmYul.UInt256.ofNat
              (tx.functionSelector % Compiler.Constants.selectorModulus)))
      (by
        simpa [prefixState, discrName, matchedName] using
          nativeSwitchPostInitFreeMemoryPrefixStoreState_discr_eq
            contract tx storage observableSlots store discrName matchedName
            selector hne hSelector)
      hSelectorRange hTagsRange hBody
  exact exec_lowerNativeSwitchBlock_postInitFreeMemory_storePrefix_tail_error_fuel
    (fuel + cases.length) switchId cases defaultBody contract tx storage
    observableSlots store err
    (by simpa [nativeSwitchTailStmts, discrName, matchedName,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCases)

/-- Post-generated-init selector-hit success when the selected body execution
    and final matched-flag fact are supplied directly. This is the
    post-`initFreeMemoryPointer` counterpart of
    `exec_lowerNativeSwitchBlock_selector_find_hit_finalMatched_store_fuel`. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_finalMatched_postInitFreeMemory_store_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
          contract tx storage observableSlots switchId store) = .ok final)
    (hFinalMatched :
      ∀ matchedName : EvmYul.Identifier,
        matchedName = Backends.nativeSwitchMatchedTempName switchId →
          final[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
        store) =
    .ok final := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  have hne := nativeSwitchDiscrTempName_ne_matchedTempName switchId
  have hCasesOnly :
      EvmYul.Yul.exec (fuel + 1 + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        (some contract)
        (nativeSwitchPostInitFreeMemoryStorePrefixStateForId contract tx
          storage observableSlots switchId store) = .ok final := by
    exact exec_nativeSwitchCaseIfs_find_hit_fuel
      (fuel + 1) selector cases tag body (some contract)
      (nativeSwitchPostInitFreeMemoryStorePrefixStateForId contract tx storage
        observableSlots switchId store) final discrName matchedName hFind
      (by
        simpa [nativeSwitchPostInitFreeMemoryStorePrefixStateForId, discrName,
          matchedName] using
          nativeSwitchPostInitFreeMemoryPrefixStoreState_matched_eq
            contract tx storage observableSlots store discrName matchedName
            (EvmYul.UInt256.ofNat
              (tx.functionSelector % Compiler.Constants.selectorModulus)))
      (by
        simpa [nativeSwitchPostInitFreeMemoryStorePrefixStateForId, discrName,
          matchedName] using
          nativeSwitchPostInitFreeMemoryPrefixStoreState_discr_eq
            contract tx storage observableSlots store discrName matchedName
            selector hne hSelector)
      hSelectorRange hTagsRange
      (by
        intro pre suffix hCases
        simpa [nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
          nativeSwitchPostInitFreeMemoryStorePrefixStateForId, discrName,
          matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hBody pre suffix hCases)
      (by simpa [matchedName] using hFinalMatched)
  have hCasesDefault :
      EvmYul.Yul.exec (fuel + 1 + cases.length + 9)
        (.Block
          (nativeSwitchCaseIfs discrName matchedName cases ++
            nativeSwitchDefaultIf matchedName defaultBody))
        (some contract)
        (nativeSwitchPostInitFreeMemoryStorePrefixStateForId contract tx
          storage observableSlots switchId store) = .ok final := by
    exact exec_nativeSwitchCaseIfs_with_default_matched_fuel
      (fuel + 1) cases defaultBody (some contract)
      (nativeSwitchPostInitFreeMemoryStorePrefixStateForId contract tx storage
        observableSlots switchId store) final discrName matchedName
      hCasesOnly
      (hFinalMatched matchedName rfl)
  exact exec_lowerNativeSwitchBlock_postInitFreeMemory_storePrefix_tail_ok_fuel
    (fuel + cases.length) switchId cases defaultBody contract tx storage
    observableSlots store final (by
      simpa [nativeSwitchTailStmts, discrName, matchedName, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm,
        nativeSwitchPostInitFreeMemoryStorePrefixStateForId] using
        hCasesDefault)

/-- Bridge-shape selector-miss endpoint on the post-`__has_selector := 1`
    state, yielding `.error Revert`. -/
theorem exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases
        [nativeRevertZeroZeroStmt]])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) =
      .error EvmYul.Yul.Exception.Revert := by
  have hEndpoint :=
    exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_fuel
      fuel selector switchId cases contract tx storage observableSlots
      ((∅ : EvmYul.Yul.VarStore).insert "__has_selector" (EvmYul.UInt256.ofNat 1))
      hSelector hFind hSelectorRange hTagsRange
  have hStateEq :
      (nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1) =
        .Ok (initialState contract tx storage observableSlots).sharedState
          ((∅ : EvmYul.Yul.VarStore).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    simp [nativeSwitchInitialOkState, EvmYul.Yul.State.insert]
  rw [hStateEq]
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  rw [hFuelEq]
  exact exec_block_cons_error (fuel + cases.length + 12) _ [] _ _
    EvmYul.Yul.Exception.Revert hEndpoint

/-- Bridge-shape selector-hit endpoint on the post-`__has_selector := 1`
    state, yielding `.error err`. Hit-case dual of
    `exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error`. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId nativeSwitchHasSelectorStore) =
        .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) =
      .error err := by
  have hEndpoint := exec_lowerNativeSwitchBlock_selector_find_hit_error_store_fuel
    fuel selector switchId tag cases defaultBody body contract tx storage
    observableSlots nativeSwitchHasSelectorStore err hSelector hFind
    hSelectorRange hTagsRange (by
      intro pre suffix hCases
      simpa [nativeSwitchStoreMarkedPrefixStateForId,
        nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
        nativeSwitchHasSelectorStore] using hBody pre suffix hCases)
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact exec_block_cons_error (fuel + cases.length + 12) _ [] _ _ err hEndpoint

/-- Bridge-shape selector-hit endpoint on the post-`__has_selector := 1`
    state, yielding the selected body's successful final state. This is the
    success dual of
    `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error`
    and derives the default-skip preservation premise from generated native
    switch freshness. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_fresh
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId nativeSwitchHasSelectorStore) = .ok final)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) =
      .ok final := by
  have hEndpoint :=
    exec_lowerNativeSwitchBlock_selector_find_hit_fresh_store_fuel
      fuel selector switchId tag cases defaultBody body contract tx storage
      observableSlots nativeSwitchHasSelectorStore final hSelector hFind
      hSelectorRange hTagsRange hFresh hBody hStmtPreserves
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact exec_block_cons_ok (fuel + cases.length + 12) _ [] _ _ final final
    hEndpoint (by simp [EvmYul.Yul.exec])

theorem exec_lowerNativeSwitchBlock_selector_find_none_without_default_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases [])
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok (nativeSwitchPrefixFinalState contract tx storage observableSlots
      (Backends.nativeSwitchDiscrTempName switchId)
      (Backends.nativeSwitchMatchedTempName switchId)) := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_fuel
  exact exec_nativeSwitchTail_find_none_without_default_fuel fuel selector
    switchId cases contract tx storage observableSlots hSelector hFind
    hSelectorRange hTagsRange

@[simp] theorem initialState_unbridgedEnvironmentDefaults
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.baseFeePerGas =
      0 ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.blobGasUsed =
      (0 : UInt64) ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.excessBlobGas =
      (0 : UInt64) ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.blobVersionedHashes =
      [] ∧
    EvmYul.State.chainId
        (initialState contract tx storage observableSlots).sharedState.toState =
      EvmYul.UInt256.ofNat EvmYul.chainId := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader, EvmYul.State.chainId]


end Compiler.Proofs.YulGeneration.Backends.Native
