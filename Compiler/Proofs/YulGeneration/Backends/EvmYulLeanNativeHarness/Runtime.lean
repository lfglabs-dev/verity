import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness.Base

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends.StateBridge
open Lean Elab Tactic Meta
open Compiler.Proofs.IRGeneration
  (IRResult IRState IRStorageSlot IRStorageWord IRTransaction)

/-- The two generated SimpleStorage selector tags fit in one EVM word. -/
private theorem simpleStorageSelectors_tagsRange
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt) :
    ∀ tag body,
      (tag, body) ∈ [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] →
        tag < EvmYul.UInt256.size := by
  intro tag body hmem
  simp at hmem
  rcases hmem with h | h
  · rcases h with ⟨rfl, rfl⟩
    norm_num [EvmYul.UInt256.size]
  · rcases h with ⟨rfl, rfl⟩
    norm_num [EvmYul.UInt256.size]

/-- Guarded selector-miss execution for the concrete SimpleStorage dispatcher
    selector set. This specializes the generic lowered-switch miss theorem to
    the two generated SimpleStorage selectors, discharging the selector tag
    word-range premise by computation. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_find_none_with_revert_default_projectResult
    (fuel selector switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind :
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].find?
          (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).success = false ∧
    (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).returnValue = none ∧
    (∀ slot,
      (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).finalStorage (IRStorageSlot.ofNat slot) =
          storage (IRStorageSlot.ofNat slot)) := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult
      fuel selector switchId
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      contract tx storage initialEvents observableSlots
      hSelector hFind hSelectorRange
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)

/-- Guarded selector-miss execution for the concrete SimpleStorage dispatcher,
    with the projected revert result exposed as one exact `YulResult`.

This packages the `revert(0, 0)` default branch in the shape needed by the
    dispatcher bridge: native execution reaches EVMYulLean's `Revert`
    exception, and Verity's projection rolls the call back to failed success,
    no return value, unchanged storage/mappings, and unchanged events. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_find_none_with_revert_default_projectResult_eq
    (fuel selector switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind :
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].find?
          (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      { success := false
        returnValue := none
        finalStorage := storage
        finalMappings := Compiler.Proofs.storageAsMappings storage
        events := initialEvents } := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq
      fuel selector switchId
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      contract tx storage initialEvents observableSlots
      hSelector hFind hSelectorRange
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)

private def simpleStorageRevertProjectedResult
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) : YulResult :=
  { success := false
    returnValue := none
    finalStorage := storage
    finalMappings := Compiler.Proofs.storageAsMappings storage
    events := initialEvents }

/-- Concrete lowered native body for the generated SimpleStorage
    `store(uint256)` selector arm. Naming this body lets later dispatcher
    bridge lemmas specialize the selector-switch theorem without carrying
    arbitrary body parameters. -/
private def simpleStorageNativeStoreBody : List EvmYul.Yul.Ast.Stmt :=
  [ .If (lowerExprNative (.call "callvalue" [])) [nativeRevertZeroZeroStmt],
    .If (lowerExprNative (.call "lt" [.call "calldatasize" [], .lit 36]))
      [nativeRevertZeroZeroStmt],
    .Let ["value"] (some (lowerExprNative (.call "calldataload" [.lit 4]))),
    .ExprStmtCall (lowerExprNative (.call "sstore" [.lit 0, .ident "value"])),
    .ExprStmtCall (lowerExprNative (.call "stop" [])) ]

/-- Concrete lowered native body for the generated SimpleStorage `retrieve()`
    selector arm. -/
private def simpleStorageNativeRetrieveBody : List EvmYul.Yul.Ast.Stmt :=
  [ .If (lowerExprNative (.call "callvalue" [])) [nativeRevertZeroZeroStmt],
    .If (lowerExprNative (.call "lt" [.call "calldatasize" [], .lit 4]))
      [nativeRevertZeroZeroStmt],
    .ExprStmtCall
      (lowerExprNative
        (.call "mstore" [.lit 0, .call "sload" [.lit 0]])),
    .ExprStmtCall (lowerExprNative (.call "return" [.lit 0, .lit 32])) ]

private def simpleStorageNativeSelectorCases :
    List (Nat × List EvmYul.Yul.Ast.Stmt) :=
  [(0x6057361d, simpleStorageNativeStoreBody),
    (0x2e64cec1, simpleStorageNativeRetrieveBody)]

/-- Guarded selector-miss execution for the concrete SimpleStorage dispatcher,
    specialized to the selector carried by the transaction.

This removes two bookkeeping premises from the default-branch bridge case:
callers no longer have to introduce a separate selector witness or prove that
the 4-byte selector fits in an EVM word. Both facts follow from the transaction
selector modulus bound used by the public end-to-end theorem. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_tx_find_none_with_revert_default_projectResult_eq
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelectorBound : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hFind : [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].find?
        (fun entry => entry.1 == tx.functionSelector % Compiler.Constants.selectorModulus) = none) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      simpleStorageRevertProjectedResult storage initialEvents := by
  exact
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_find_none_with_revert_default_projectResult_eq
      fuel (tx.functionSelector % Compiler.Constants.selectorModulus) switchId
      storeBody retrieveBody contract tx storage initialEvents observableSlots
      rfl hFind
      (by
        have hmod :
            tx.functionSelector % Compiler.Constants.selectorModulus =
              tx.functionSelector :=
          Nat.mod_eq_of_lt hSelectorBound
        have hModulus :
            Compiler.Constants.selectorModulus < EvmYul.UInt256.size := by
          norm_num [Compiler.Constants.selectorModulus, EvmYul.UInt256.size]
        rw [hmod]
        omega) |>.imp_right (by intro h; simp [simpleStorageRevertProjectedResult] at h ⊢)

/-- Guarded selector-miss execution for the concrete SimpleStorage dispatcher,
    using the semantic selector disequalities instead of the raw generated
    selector-table lookup.

This is the branch shape needed by the dispatcher bridge case split: once the
transaction selector is known to be neither generated selector, the concrete
`find? = none` premise is discharged internally before executing the actual
native lowered switch relation. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_tx_miss_with_revert_default_projectResult_eq
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelectorBound : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNotStore : tx.functionSelector ≠ 0x6057361d)
    (hNotRetrieve : tx.functionSelector ≠ 0x2e64cec1) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      simpleStorageRevertProjectedResult storage initialEvents := by
  apply
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_tx_find_none_with_revert_default_projectResult_eq
      fuel switchId storeBody retrieveBody contract tx storage initialEvents
      observableSlots hSelectorBound
  have hMod := Nat.mod_eq_of_lt hSelectorBound
  simp [hMod]
  constructor
  · intro h
    exact hNotStore h.symm
  · intro h
    exact hNotRetrieve h.symm

/-- Guarded selector-miss execution for the concrete lowered SimpleStorage
    selector switch, with both generated selector bodies fixed to their native
    lowered shapes. This is the default branch theorem needed by the bridge
    once the outer dispatcher has exposed the inner selector switch. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageConcrete_tx_miss_with_revert_default_projectResult_eq
    (fuel switchId : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelectorBound : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNotStore : tx.functionSelector ≠ 0x6057361d)
    (hNotRetrieve : tx.functionSelector ≠ 0x2e64cec1) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, simpleStorageNativeStoreBody),
          (0x2e64cec1, simpleStorageNativeRetrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, simpleStorageNativeStoreBody),
            (0x2e64cec1, simpleStorageNativeRetrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      simpleStorageRevertProjectedResult storage initialEvents := by
  exact
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_tx_miss_with_revert_default_projectResult_eq
      fuel switchId simpleStorageNativeStoreBody simpleStorageNativeRetrieveBody
      contract tx storage initialEvents observableSlots hSelectorBound
      hNotStore hNotRetrieve

/-- Store-selector hit execution for the concrete SimpleStorage dispatcher
    selector set. This specializes the generic lowered-switch hit theorem to
    `store(uint256)`, discharging the computed selector lookup and selector tag
    word-range premises. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_error_fuel
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hBody : ∀ pre suffix,
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] =
          pre ++ (0x6057361d, storeBody) :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
          (.Block storeBody) (some contract)
          ((nativeSwitchPrefixFinalState contract tx storage observableSlots
            (Backends.nativeSwitchDiscrTempName switchId)
            (Backends.nativeSwitchMatchedTempName switchId)).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error err := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_hit_error_fuel
      fuel 0x6057361d switchId
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      [nativeRevertZeroZeroStmt] 0x6057361d storeBody contract tx storage
      observableSlots err hSelector
      (by simp)
      (by norm_num [EvmYul.UInt256.size])
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)
      hBody

/-- Store-prefix variant of `_simpleStorageSelectors_store_hit_error_fuel`,
    lifting the SimpleStorage store-hit selector specialization to states
    already carrying additional bindings (e.g. the dispatcher's
    `__has_selector := 1`). -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_error_store_fuel
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hBody : ∀ pre suffix,
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] =
          pre ++ (0x6057361d, storeBody) :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
          (.Block storeBody) (some contract)
          ((((.Ok (initialState contract tx storage observableSlots).sharedState
                  store : EvmYul.Yul.State).insert
                (Backends.nativeSwitchDiscrTempName switchId)
                (EvmYul.UInt256.ofNat
                  (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 0)).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState store) =
      .error err := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_hit_error_store_fuel
      fuel 0x6057361d switchId 0x6057361d
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      [nativeRevertZeroZeroStmt] storeBody contract tx storage
      observableSlots store err hSelector
      (by simp)
      (by norm_num [EvmYul.UInt256.size])
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)
      hBody

private def simpleStorageStoreHaltProjectedResult
    (tx : YulTransaction)
    (initialEvents : List (List Nat))
    (haltState : EvmYul.Yul.State) : YulResult :=
  { success := true
    returnValue := none
    finalStorage := projectStorageFromState tx haltState
    finalMappings :=
      Compiler.Proofs.storageAsMappings (projectStorageFromState tx haltState)
    events := initialEvents ++ projectLogsFromState haltState }

/-- Store-selector hit execution for the concrete SimpleStorage dispatcher,
    packaged with the exact projected result of the selected setter body.

This removes the switch-case wrapper from later bridge obligations: callers can
prove the selected body once for every possible decomposition, then consume one
exact native `YulResult` equality at the full lowered-switch boundary. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_projectResult_eq
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (haltState : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hBody : ∀ pre suffix,
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] =
          pre ++ (0x6057361d, storeBody) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
        (.Block storeBody) (some contract)
        (nativeSwitchMarkedPrefixStateForId contract tx storage
          observableSlots switchId) =
          .error (EvmYul.Yul.Exception.YulHalt haltState haltValue))
    (hProject :
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageStoreHaltProjectedResult tx initialEvents haltState) :
      EvmYul.Yul.exec
          (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
          (Backends.lowerNativeSwitchBlock
            Compiler.Proofs.YulGeneration.selectorExpr
            switchId
            [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
            [nativeRevertZeroZeroStmt])
          (some contract)
          (nativeSwitchInitialOkState contract tx storage observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageStoreHaltProjectedResult tx initialEvents haltState := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq
      fuel 0x6057361d switchId
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      [nativeRevertZeroZeroStmt] 0x6057361d storeBody contract tx storage
      initialEvents observableSlots
      (EvmYul.Yul.Exception.YulHalt haltState haltValue)
      (simpleStorageStoreHaltProjectedResult tx initialEvents haltState)
      hSelector (by simp) (by norm_num [EvmYul.UInt256.size])
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)
      hBody hProject

/-- Concrete SimpleStorage store-selector hit execution. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageConcrete_store_hit_projectResult_eq
    (fuel switchId : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (haltState : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hSelectorBound : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelector : tx.functionSelector = 0x6057361d)
    (hBody : ∀ pre suffix,
      simpleStorageNativeSelectorCases =
          pre ++ (0x6057361d, simpleStorageNativeStoreBody) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
        (.Block simpleStorageNativeStoreBody) (some contract)
        (nativeSwitchMarkedPrefixStateForId contract tx storage
          observableSlots switchId) =
          .error (EvmYul.Yul.Exception.YulHalt haltState haltValue))
    (hProject :
      projectResult tx storage initialEvents (.error
          (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageStoreHaltProjectedResult tx initialEvents haltState) :
      EvmYul.Yul.exec
          (fuel + simpleStorageNativeSelectorCases.length + 12)
          (Backends.lowerNativeSwitchBlock
            Compiler.Proofs.YulGeneration.selectorExpr
            switchId simpleStorageNativeSelectorCases [nativeRevertZeroZeroStmt])
          (some contract)
          (nativeSwitchInitialOkState contract tx storage observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents (.error
          (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageStoreHaltProjectedResult tx initialEvents haltState := by
  have hMod :
      tx.functionSelector % Compiler.Constants.selectorModulus =
        tx.functionSelector :=
    Nat.mod_eq_of_lt hSelectorBound
  exact
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_projectResult_eq
      fuel switchId simpleStorageNativeStoreBody simpleStorageNativeRetrieveBody
      contract tx storage initialEvents observableSlots haltState haltValue
      (by rw [hMod, hSelector])
      (by simpa [simpleStorageNativeSelectorCases] using hBody) hProject

/-- Retrieve-selector hit execution for the concrete SimpleStorage dispatcher. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_retrieve_hit_error_fuel
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector :
      0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hBody : ∀ pre suffix,
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] =
          pre ++ (0x2e64cec1, retrieveBody) :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
          (.Block retrieveBody) (some contract)
          ((nativeSwitchPrefixFinalState contract tx storage observableSlots
            (Backends.nativeSwitchDiscrTempName switchId)
            (Backends.nativeSwitchMatchedTempName switchId)).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error err := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_hit_error_fuel
      fuel 0x2e64cec1 switchId
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      [nativeRevertZeroZeroStmt] 0x2e64cec1 retrieveBody contract tx storage
      observableSlots err hSelector
      (by simp)
      (by norm_num [EvmYul.UInt256.size])
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)
      hBody

private def simpleStorageRetrieveHaltProjectedResult
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (haltState : EvmYul.Yul.State) : YulResult :=
  { success := true
    returnValue :=
      if 0 ∈ observableSlots then
        some (uint256ToNat (storage 0))
      else
        some 0
    finalStorage := projectStorageFromState tx haltState
    finalMappings :=
      Compiler.Proofs.storageAsMappings (projectStorageFromState tx haltState)
    events := initialEvents ++ projectLogsFromState haltState }

/-- Retrieve-selector hit execution for the concrete SimpleStorage dispatcher,
    packaged with the exact projected result of the selected getter body. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_retrieve_hit_projectResult_eq
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (initialEvents : List (List Nat))
    (observableSlots : List Nat) (haltState : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hBody : ∀ pre suffix,
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] =
          pre ++ (0x2e64cec1, retrieveBody) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
        (.Block retrieveBody) (some contract)
        (nativeSwitchMarkedPrefixStateForId contract tx storage
          observableSlots switchId) =
          .error (EvmYul.Yul.Exception.YulHalt haltState haltValue))
    (hProject :
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageRetrieveHaltProjectedResult tx storage initialEvents
          observableSlots haltState) :
      EvmYul.Yul.exec
          (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
          (Backends.lowerNativeSwitchBlock
            Compiler.Proofs.YulGeneration.selectorExpr
            switchId
            [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
            [nativeRevertZeroZeroStmt])
          (some contract)
          (nativeSwitchInitialOkState contract tx storage observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageRetrieveHaltProjectedResult tx storage initialEvents
          observableSlots haltState := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq
      fuel 0x2e64cec1 switchId
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      [nativeRevertZeroZeroStmt] 0x2e64cec1 retrieveBody contract tx storage
      initialEvents observableSlots
      (EvmYul.Yul.Exception.YulHalt haltState haltValue)
      (simpleStorageRetrieveHaltProjectedResult tx storage initialEvents
        observableSlots haltState)
      hSelector (by simp) (by norm_num [EvmYul.UInt256.size])
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)
      hBody hProject

/-- Concrete SimpleStorage retrieve-selector hit execution. -/
private theorem exec_lowerNativeSwitchBlock_simpleStorageConcrete_retrieve_hit_projectResult_eq
    (fuel switchId : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (haltState : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hSelectorBound : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelector : tx.functionSelector = 0x2e64cec1)
    (hBody : ∀ pre suffix,
      simpleStorageNativeSelectorCases =
          pre ++ (0x2e64cec1, simpleStorageNativeRetrieveBody) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
        (.Block simpleStorageNativeRetrieveBody) (some contract)
        (nativeSwitchMarkedPrefixStateForId contract tx storage
          observableSlots switchId) =
          .error (EvmYul.Yul.Exception.YulHalt haltState haltValue))
    (hProject :
      projectResult tx storage initialEvents (.error
          (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageRetrieveHaltProjectedResult tx storage initialEvents
          observableSlots haltState) :
      EvmYul.Yul.exec
          (fuel + simpleStorageNativeSelectorCases.length + 12)
          (Backends.lowerNativeSwitchBlock
            Compiler.Proofs.YulGeneration.selectorExpr
            switchId simpleStorageNativeSelectorCases [nativeRevertZeroZeroStmt])
          (some contract)
          (nativeSwitchInitialOkState contract tx storage observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents (.error
          (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageRetrieveHaltProjectedResult tx storage initialEvents
          observableSlots haltState := by
  have hMod := Nat.mod_eq_of_lt hSelectorBound
  exact
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_retrieve_hit_projectResult_eq
      fuel switchId simpleStorageNativeStoreBody simpleStorageNativeRetrieveBody
      contract tx storage initialEvents observableSlots haltState haltValue
      (by rw [hMod, hSelector])
      (by simpa [simpleStorageNativeSelectorCases] using hBody) hProject

@[simp] theorem projectResult_finalMappings
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (result :
      Except EvmYul.Yul.Exception
        (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal)) :
    (projectResult tx initialStorage initialEvents result).finalMappings =
      Compiler.Proofs.storageAsMappings
        (projectResult tx initialStorage initialEvents result).finalStorage := by
  cases result with
  | ok value =>
      cases value with
      | mk state values => rfl
  | error err =>
      cases err <;> rfl

/-- Lower and execute Verity runtime Yul through EVMYulLean's native
    dispatcher. -/
def interpretRuntimeNative
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat) := []) :
    Except NativeLoweringError YulResult := do
  validateGeneratedRuntimeNativeFragment runtimeCode
  let contract ← lowerRuntimeContractNative runtimeCode
  validateNativeRuntimeEnvironment runtimeCode tx
  let initial :=
    initialState contract tx storage
      (materializedStorageSlots runtimeCode observableSlots)
  let result := EvmYul.Yul.callDispatcher fuel (some contract) initial
  pure (projectResult tx storage events result)

@[simp] theorem interpretRuntimeNative_loweringError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (err : NativeLoweringError)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .error err) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error err := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_ok runtimeCode hFragment, hLower]
  rfl

@[simp] theorem interpretRuntimeNative_generatedFragmentError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (hFragment : generatedRuntimeNativeFragment runtimeCode = false) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error unsupportedGeneratedRuntimeNativeFragmentError := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_error runtimeCode hFragment]
  rfl

@[simp] theorem interpretRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .ok ()) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .ok (projectResult tx storage events
        (EvmYul.Yul.callDispatcher fuel (some contract)
          (initialState contract tx storage
            (materializedStorageSlots runtimeCode observableSlots)))) := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_ok runtimeCode hFragment,
    hLower, hEnv]
  rfl

@[simp] theorem interpretRuntimeNative_succ_eq_contractDispatcherBlockResult_of_lowerRuntimeContractNative
    (fuel' : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .ok ()) :
    interpretRuntimeNative (Nat.succ fuel') runtimeCode tx storage observableSlots events =
      .ok (projectResult tx storage events
        (contractDispatcherBlockResult fuel' contract
          (initialState contract tx storage
            (materializedStorageSlots runtimeCode observableSlots)))) := by
  rw [interpretRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
    (fuel := Nat.succ fuel') (contract := contract)
    (hFragment := hFragment) (hLower := hLower) (hEnv := hEnv)]
  rw [callDispatcher_succ_eq_callDispatcherBlockResult]
  rw [callDispatcherBlockResult_initialState_eq_contractDispatcherBlockResult]

@[simp] theorem interpretRuntimeNative_succ_eq_contractDispatcherExecResult_of_lowerRuntimeContractNative
    (fuel' : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .ok ()) :
    interpretRuntimeNative (Nat.succ fuel') runtimeCode tx storage observableSlots events =
      .ok (projectResult tx storage events
        (let initial :=
          initialState contract tx storage
            (materializedStorageSlots runtimeCode observableSlots)
        let dispatcherDef :=
          EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [contract.dispatcher]
        match contractDispatcherExecResult fuel' contract initial with
        | .error err => .error err
        | .ok finalState =>
            let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
            .ok (restored, List.map finalState.lookup! dispatcherDef.rets))) := by
  rw [interpretRuntimeNative_succ_eq_contractDispatcherBlockResult_of_lowerRuntimeContractNative
    (contract := contract) (hFragment := hFragment) (hLower := hLower) (hEnv := hEnv)]
  rw [contractDispatcherBlockResult_eq_execResult]
  rfl

@[simp] theorem interpretRuntimeNative_environmentError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (err : NativeLoweringError)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .error err) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error err := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_ok runtimeCode hFragment,
    hLower, hEnv]
  rfl

/-- Native EVMYulLean execution target for emitted IR-contract runtime Yul.

This is the executable target that #1737 will promote into the public theorem
path once the state/result bridge lemmas are proved. It intentionally returns
`Except NativeLoweringError YulResult` today because native lowering can still fail
closed for duplicate helper definitions or unsupported runtime shapes.

The observable slot set is explicit because the public theorem compares only
those final storage (IRStorageSlot.ofNat slot)s. Native execution materializes those slots plus
literal `sload` slots derived from the emitted runtime so storage reads remain
faithful even when callers compare a smaller public projection.
-/
def interpretIRRuntimeNative
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat) :
    Except NativeLoweringError YulResult :=
  interpretRuntimeNative fuel (Compiler.emitYul contract).runtimeCode
    (YulTransaction.ofIR tx) state.storage observableSlots state.events

@[simp] theorem interpretIRRuntimeNative_eq_interpretRuntimeNative
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat) :
    interpretIRRuntimeNative fuel contract tx state observableSlots =
      interpretRuntimeNative fuel (Compiler.emitYul contract).runtimeCode
        (YulTransaction.ofIR tx) state.storage observableSlots state.events := by
  rfl

@[simp] theorem interpretIRRuntimeNative_loweringError
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (err : NativeLoweringError)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul contract).runtimeCode = true)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul contract).runtimeCode =
      .error err) :
    interpretIRRuntimeNative fuel contract tx state observableSlots = .error err := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative,
    validateGeneratedRuntimeNativeFragment_ok (Compiler.emitYul contract).runtimeCode
      hFragment, hLower]
  rfl

@[simp] theorem interpretIRRuntimeNative_generatedFragmentError
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul contract).runtimeCode = false) :
    interpretIRRuntimeNative fuel contract tx state observableSlots =
      .error unsupportedGeneratedRuntimeNativeFragmentError := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative,
    validateGeneratedRuntimeNativeFragment_error (Compiler.emitYul contract).runtimeCode
      hFragment]
  rfl

@[simp] theorem interpretIRRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
    (fuel : Nat)
    (irContract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul irContract).runtimeCode = true)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul irContract).runtimeCode =
      .ok nativeContract)
    (hEnv :
      validateNativeRuntimeEnvironment (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ()) :
    interpretIRRuntimeNative fuel irContract tx state observableSlots =
      .ok (projectResult (YulTransaction.ofIR tx) state.storage state.events
        (EvmYul.Yul.callDispatcher fuel (some nativeContract)
          (initialState nativeContract (YulTransaction.ofIR tx) state.storage
            (materializedStorageSlots (Compiler.emitYul irContract).runtimeCode
              observableSlots)))) := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative,
    validateGeneratedRuntimeNativeFragment_ok (Compiler.emitYul irContract).runtimeCode
      hFragment, hLower, hEnv]
  rfl

@[simp] theorem interpretIRRuntimeNative_succ_eq_contractDispatcherBlockResult_of_lowerRuntimeContractNative
    (fuel' : Nat)
    (irContract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul irContract).runtimeCode = true)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul irContract).runtimeCode =
      .ok nativeContract)
    (hEnv :
      validateNativeRuntimeEnvironment (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ()) :
    interpretIRRuntimeNative (Nat.succ fuel') irContract tx state observableSlots =
      .ok (projectResult (YulTransaction.ofIR tx) state.storage state.events
        (contractDispatcherBlockResult fuel' nativeContract
          (initialState nativeContract (YulTransaction.ofIR tx) state.storage
            (materializedStorageSlots (Compiler.emitYul irContract).runtimeCode
              observableSlots)))) := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative_succ_eq_contractDispatcherBlockResult_of_lowerRuntimeContractNative
    (contract := nativeContract) (hFragment := hFragment) (hLower := hLower)
    (hEnv := hEnv)]

@[simp] theorem interpretIRRuntimeNative_succ_eq_contractDispatcherExecResult_of_lowerRuntimeContractNative
    (fuel' : Nat)
    (irContract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul irContract).runtimeCode = true)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul irContract).runtimeCode =
      .ok nativeContract)
    (hEnv :
      validateNativeRuntimeEnvironment (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ()) :
    interpretIRRuntimeNative (Nat.succ fuel') irContract tx state observableSlots =
      .ok (projectResult (YulTransaction.ofIR tx) state.storage state.events
        (let initial :=
          initialState nativeContract (YulTransaction.ofIR tx) state.storage
            (materializedStorageSlots (Compiler.emitYul irContract).runtimeCode
              observableSlots)
        let dispatcherDef :=
          EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [nativeContract.dispatcher]
        match contractDispatcherExecResult fuel' nativeContract initial with
        | .error err => .error err
        | .ok finalState =>
            let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
            .ok (restored, List.map finalState.lookup! dispatcherDef.rets))) := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative_succ_eq_contractDispatcherExecResult_of_lowerRuntimeContractNative
    (contract := nativeContract) (hFragment := hFragment) (hLower := hLower)
    (hEnv := hEnv)]

/-- Result comparison surface for the native EVMYulLean harness.

The native harness can still fail closed during Verity-Yul-to-EVMYulLean
lowering, so native-facing theorem statements record both that native execution
returns a `YulResult` and that this result matches IR execution. -/
private def nativeResultsMatch
    (ir : IRResult)
    (native : Except NativeLoweringError YulResult) :
    Prop :=
  match native with
  | .ok yul =>
      ir.success = yul.success ∧
      ir.returnValue = yul.returnValue ∧
      (∀ slot, ir.finalStorage slot = yul.finalStorage slot) ∧
      (∀ base key, ir.finalMappings base key = yul.finalMappings base key) ∧
      ir.events = yul.events
  | .error _ => False

/-- Observable result comparison surface for native EVMYulLean execution. -/
def nativeResultsMatchOn
    (observableSlots : List Nat)
    (ir : IRResult)
    (native : Except NativeLoweringError YulResult) :
    Prop :=
  match native with
  | .ok yul =>
      ir.success = yul.success ∧
      ir.returnValue = yul.returnValue ∧
      (∀ slot, slot ∈ observableSlots →
        ir.finalStorage (IRStorageSlot.ofNat slot) =
          yul.finalStorage (IRStorageSlot.ofNat slot)) ∧
      ir.events = yul.events
  | .error _ => False

/-- Variant of `exec_block_leave_ok_add_ten` that splices a
`NativePreservableStraightStmts`-derived prefix in front of `.Leave`.

If the native lowering of the prefix evaluates to `.ok mid` at the
`fuel + suffixLen + 10` budget already used by the dispatcher harness, then
appending `.Leave` to the lowered prefix runs at
`fuel + suffixLen + native.length + 10` and produces `.ok mid.setLeave`. -/
theorem exec_block_lowerStmtsNativeWithSwitchIds_with_leave_ok_eq_of_NativeBlockPreservesWord
    (fuel suffixLen : Nat)
    (native : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (initial mid : EvmYul.Yul.State)
    (hPre :
      EvmYul.Yul.exec (fuel + suffixLen + native.length + 10)
          (.Block native) codeOverride initial = .ok mid) :
    EvmYul.Yul.exec (fuel + suffixLen + native.length + 10)
        (.Block (native ++ [.Leave])) codeOverride initial =
      .ok mid.setLeave := by
  have hFuel :
      fuel + suffixLen + native.length + 10 =
        (fuel + suffixLen + 9) + native.length + 1 := by omega
  have hLeft :
      EvmYul.Yul.exec ((fuel + suffixLen + 9) + native.length + 1)
          (.Block native) codeOverride initial = .ok mid := hFuel ▸ hPre
  have hRight :
      EvmYul.Yul.exec ((fuel + suffixLen + 9) + 1) (.Block [.Leave])
          codeOverride mid = .ok mid.setLeave := by
    have hLeaveFuel :
        (fuel + suffixLen + 9) + 1 =
          Nat.succ (Nat.succ (fuel + suffixLen + 8)) := by
      omega
    rw [hLeaveFuel]
    cases mid <;> simp [EvmYul.Yul.exec, EvmYul.Yul.State.setLeave]
  rw [hFuel]
  exact exec_block_append_ok (fuel + suffixLen + 9) 1 native [.Leave]
    codeOverride initial mid mid.setLeave hLeft hRight

/-- No-leave variant: a `.Block (lower preStmts)` with per-slot preservation
exits with `.ok mid`, packaged at the standard `+ 10` fuel-padding form so
the dispatcher harness can splice it into a switch case body.

This is the trivial fuel-padded form of the prefix execution: given that the
lowered prefix already evaluates to `.ok mid`, restating the equation at the
canonical `fuel + suffixLen + native.length + 10` budget keeps the consumer
free of fuel-arithmetic plumbing. -/
theorem exec_block_lowerStmtsNativeWithSwitchIds_ok_eq_of_NativeBlockPreservesWord
    (fuel suffixLen : Nat)
    (native : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (initial mid : EvmYul.Yul.State)
    (hPre :
      EvmYul.Yul.exec (fuel + suffixLen + native.length + 10)
          (.Block native) codeOverride initial = .ok mid) :
    EvmYul.Yul.exec (fuel + suffixLen + native.length + 10)
        (.Block (native ++ [])) codeOverride initial = .ok mid := by
  simpa [List.append_nil] using hPre

end Compiler.Proofs.YulGeneration.Backends.Native
