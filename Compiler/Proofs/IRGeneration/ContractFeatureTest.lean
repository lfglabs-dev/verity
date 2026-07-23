import Compiler.Proofs.IRGeneration.Contract
import Compiler.Proofs.MappingSlot

namespace Compiler.Proofs.IRGeneration.ContractFeatureTest

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration
open Compiler.Yul

private def literalMappingWriteFunction : FunctionSpec :=
  { name := "setFive"
    params := [{ name := "value", ty := .uint256 }]
    returnType := none
    body := [Stmt.setMapping "balances" (.literal 5) (.param "value"), .stop] }

private def literalMappingWriteSpec : CompilationModel :=
  { name := "LiteralMappingWrite"
    fields := [{ name := "balances", ty := .mappingTyped (.simple .uint256), slot := some 7 }]
    constructor := none
    functions := [literalMappingWriteFunction] }

private def literalMappingWriteSelector : Nat := 0x11111111

private theorem literalMappingWrite_noPackedFields :
    ∀ field ∈ literalMappingWriteSpec.fields, field.packedBits = none := by
  intro field hfield
  simp [literalMappingWriteSpec] at hfield
  rcases hfield with rfl
  rfl

private theorem literalMappingWrite_noFallback :
    ∀ fn ∈ literalMappingWriteSpec.functions, fn.name != "fallback" := by
  intro fn hfn
  simp [literalMappingWriteSpec] at hfn
  rcases hfn with rfl
  decide

private theorem literalMappingWrite_noReceive :
    ∀ fn ∈ literalMappingWriteSpec.functions, fn.name != "receive" := by
  intro fn hfn
  simp [literalMappingWriteSpec] at hfn
  rcases hfn with rfl
  decide

private def literalMappingWrite_supported_function :
    ∀ fn, fn ∈ literalMappingWriteSpec.functions →
      SupportedFunctionExceptMappingWrites literalMappingWriteSpec fn := by
  intro fn hfn
  simp [literalMappingWriteSpec] at hfn
  rcases hfn with rfl
  exact
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      noNonReentrant := rfl
      params :=
        { namesNodup := by decide
          supported := by
            intro param hparam
            rcases (by simpa [literalMappingWriteFunction] using hparam : param = { name := "value", ty := .uint256 }) with rfl
            trivial
          calldataThreshold := by decide }
      returns := { resolved := ⟨[], rfl, trivial⟩ }
      body :=
        { stmtList :=
            .append
              (.setMappingSingle
                (.literal 5)
                (by simp [FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames])
                (.param "value")
                (by
                  intro name hname
                  simp [FunctionBody.exprBoundNames, literalMappingWriteFunction] at hname ⊢
                  aesop)
                rfl)
              (.terminalCore (.stop .nil))
          core := { surfaceClosed := by decide }
          state := { surfaceClosed := by decide }
          calls :=
            { helpers :=
                { helperRank := 0
                  callNamesNodup := helperCallNames_nodup _
                  summaryOf := by
                    intro calleeName hmem
                    exfalso
                    simpa [literalMappingWriteFunction, helperCallNames,
                      stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
                      exprInternalHelperCallNames] using hmem
                  calleeRanksDecrease := by
                    intro calleeName hmem
                    exfalso
                    simpa [literalMappingWriteFunction, helperCallNames,
                      stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
                      exprInternalHelperCallNames] using hmem
                  exprCallsPreserveWorld := by
                    intro calleeName hmem
                    exfalso
                    simpa [literalMappingWriteFunction, exprHelperCallNames,
                      stmtListExprHelperCallNames, stmtExprHelperCallNames,
                      exprInternalHelperCallNames] using hmem }
              foreign := by decide
              lowLevel := by decide }
          effects := { surfaceClosed := by decide }
          noLocalObligations := rfl } }

private def literalMappingWrite_supported_spec :
    SupportedSpecExceptMappingWrites literalMappingWriteSpec [literalMappingWriteSelector] :=
  { invariants :=
      { normalizedFields := rfl
        noPackedFields := literalMappingWrite_noPackedFields
        selectorCount := by decide
        selectorsDistinct := by decide
        functionNamesNodup := by decide }
    surface :=
      { noEvents := rfl
        noErrors := rfl
        noExternals := rfl
        noAdtTypes := rfl
        noCheckedArithmetic := by
          simp [contractUsesCheckedArithmetic, literalMappingWriteSpec,
            literalMappingWriteFunction, stmtListMayUseCheckedArithmetic,
            stmtMayUseCheckedArithmetic]
        noTemplateIntrinsics := by
          rw [templateIntrinsicItems, literalMappingWriteSpec, literalMappingWriteFunction]
          unfold collectTemplateIntrinsicsFromStmts
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [collectTemplateIntrinsicsFromStmt.eq_def]
          simp only [Stmt.directMetadata, Stmt.childLists, List.attach_nil,
            List.flatMap_nil, List.append_nil]
          simp only [List.flatMap_cons, List.flatMap_nil]
          rw [collectTemplateIntrinsicsFromExpr.eq_def]
          rw [collectTemplateIntrinsicsFromExpr.eq_def]
          simp [Expr.children]
          rw [collectTemplateIntrinsicsFromStmt.eq_def]
          simp [Stmt.directMetadata, Stmt.childLists]
        noFallback := literalMappingWrite_noFallback
        noReceive := literalMappingWrite_noReceive }
    constructor := by
      intro ctor hctor
      simp [literalMappingWriteSpec] at hctor
    functions := literalMappingWrite_supported_function }

private theorem literalMappingWrite_noConflict :
    firstFieldWriteSlotConflict literalMappingWriteSpec.fields = none := by
  native_decide

private def literalMappingWriteTx : IRTransaction :=
  { sender := 9
    functionSelector := literalMappingWriteSelector
    args := [23] }

private def constructorOnlyCtor : ConstructorSpec :=
  { params := [{ name := "initialOwner", ty := .address }]
    body := [Stmt.setStorageAddr "owner" (.param "initialOwner"), .stop] }

private def constructorBodyFunction : FunctionSpec :=
  constructorAsFunctionSpec constructorOnlyCtor

private def constructorOnlyOwnerField : Field :=
  { name := "owner", ty := .address }

private def constructorOnlySpec : CompilationModel :=
  { name := "ConstructorOnly"
    fields := [constructorOnlyOwnerField]
    constructor := some constructorOnlyCtor
    functions := [] }

private theorem constructorOnly_owner_resolved :
    findFieldWithResolvedSlot constructorOnlySpec.fields "owner" =
      some ({ name := "owner", ty := FieldType.address }, 0) := by
  rfl

private theorem constructorOnly_owner_resolved_lit :
    findFieldWithResolvedSlot [{ name := "owner", ty := FieldType.address }] "owner" =
      some ({ name := "owner", ty := FieldType.address }, 0) := by
  rfl

private def constructorOnlySupported :
    SupportedConstructor constructorOnlySpec constructorOnlyCtor :=
  { params :=
      { namesNodup := by decide
        supported := by
          intro param hparam
          simp [constructorOnlyCtor] at hparam
          rcases hparam with rfl
          trivial
        calldataThreshold := by decide }
    body :=
      { stmtList :=
          .append
            (.setStorageAddrSingleSlot
              (fieldName := "owner")
              (slot := 0)
              (.param "initialOwner")
              (by
                intro name hname
                have hparam : name = "initialOwner" := by
                  simpa [FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames] using hname
                simp [constructorAsFunctionSpec, constructorOnlyCtor, constructorArgAliasNames, hparam])
              (by
                simpa [constructorOnlySpec, constructorOnlyOwnerField] using
                  (findFieldWithResolvedSlot_cons constructorOnlyOwnerField [] "owner")))
            (.terminalCore (.stop .nil))
        core := { surfaceClosed := by decide }
        state := { surfaceClosed := by decide }
        calls :=
          { helpers :=
              { helperRank := 0
                callNamesNodup := helperCallNames_nodup _
                summaryOf := by
                  intro calleeName hmem
                  exfalso
                  simpa [helperCallNames, constructorAsFunctionSpec, constructorOnlyCtor,
                    stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
                    exprInternalHelperCallNames] using hmem
                calleeRanksDecrease := by
                  intro calleeName hmem
                  exfalso
                  simpa [helperCallNames, constructorAsFunctionSpec, constructorOnlyCtor,
                    stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
                    exprInternalHelperCallNames] using hmem
                exprCallsPreserveWorld := by
                  intro calleeName hmem
                  exfalso
                  simpa [exprHelperCallNames, constructorAsFunctionSpec, constructorOnlyCtor,
                    stmtListExprHelperCallNames, stmtExprHelperCallNames,
                    exprInternalHelperCallNames] using hmem }
            foreign := by decide
            lowLevel := by decide }
        effects := { surfaceClosed := by decide }
        noLocalObligations := rfl }
    rawCalldataSurfaceClosed := by decide }

private def constructorOnlyTx : IRTransaction :=
  { sender := 7
    functionSelector := 0
    args := [11] }

private def constructorOnlyTrailingTx : IRTransaction :=
  { constructorOnlyTx with args := [11, 99] }

private def constructorArgCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body := [Stmt.setStorage "value" (.constructorArg 0), .stop] }

private def constructorArgSpec : CompilationModel :=
  { name := "ConstructorArg"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorArgCtor
    functions := [] }

private def constructorArgTx : IRTransaction :=
  { sender := 5
    functionSelector := 0
    args := [13] }

private def constructorArgTrailingTx : IRTransaction :=
  { sender := 5
    functionSelector := 0
    args := [13, 99] }

private def constructorCalldataCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body := [Stmt.setStorage "value" .calldatasize, .stop] }

private def constructorCalldataSpec : CompilationModel :=
  { name := "ConstructorCalldata"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorCalldataCtor
    functions := [] }

private def constructorCalldataTx : IRTransaction :=
  { sender := 6
    functionSelector := 0
    args := [21] }

example :
    (SourceSemantics.withConstructorTransactionContext
      Verity.defaultState
      constructorCalldataTx).calldataSize.val = 32 := by
  native_decide

example :
    (SourceSemantics.withTransactionContext
      Verity.defaultState
      constructorCalldataTx).calldataSize.val = 36 := by
  native_decide

private def constructorRightCalldataCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body := [Stmt.setStorage "value" (.add (.literal 1) .calldatasize), .stop] }

private def constructorRightCalldataSpec : CompilationModel :=
  { name := "ConstructorRightCalldata"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorRightCalldataCtor
    functions := [] }

private def constructorRightCalldataloadCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body := [Stmt.setStorage "value" (.add (.literal 1) (.calldataload (.literal 0))), .stop] }

private def constructorRightCalldataloadSpec : CompilationModel :=
  { name := "ConstructorRightCalldataload"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorRightCalldataloadCtor
    functions := [] }

private def constructorHelperArgCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body :=
      [Stmt.internalCallAssign ["tmp"] "identity" [.constructorArg 0],
        Stmt.setStorage "value" (.localVar "tmp"),
        .stop] }

private def constructorHelperArgTx : IRTransaction :=
  { sender := 8
    functionSelector := 0
    args := [17] }

private def identityInternalHelper : FunctionSpec :=
  { name := "identity"
    params := [{ name := "x", ty := .uint256 }]
    returnType := some .uint256
    isInternal := true
    body := [Stmt.return (.param "x")] }

private def constructorHelperArgSpec : CompilationModel :=
  { name := "ConstructorHelperArg"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorHelperArgCtor
    functions := [identityInternalHelper] }

private def rawSizeInternalHelper : FunctionSpec :=
  { name := "rawSize"
    params := []
    returnType := some .uint256
    isInternal := true
    body := [Stmt.return .calldatasize] }

private def constructorHelperRawCalldataCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body :=
      [Stmt.internalCallAssign ["tmp"] "rawSize" [],
        Stmt.setStorage "value" (.localVar "tmp"),
        .stop] }

private def constructorHelperRawCalldataSpec : CompilationModel :=
  { name := "ConstructorHelperRawCalldata"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorHelperRawCalldataCtor
    functions := [rawSizeInternalHelper] }

private def nestedRawSizeInternalHelper : FunctionSpec :=
  { name := "nestedRawSize"
    params := []
    returnType := some .uint256
    isInternal := true
    body := [Stmt.internalCallAssign ["tmp"] "rawSize" [], Stmt.return (.localVar "tmp")] }

private def constructorNestedHelperRawCalldataCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body :=
      [Stmt.internalCallAssign ["tmp"] "nestedRawSize" [],
        Stmt.setStorage "value" (.localVar "tmp"),
        .stop] }

private def constructorNestedHelperRawCalldataSpec : CompilationModel :=
  { name := "ConstructorNestedHelperRawCalldata"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorNestedHelperRawCalldataCtor
    functions := [nestedRawSizeInternalHelper, rawSizeInternalHelper] }

private def recursiveNoRawInternalHelper : FunctionSpec :=
  { name := "recursiveNoRaw"
    params := []
    returnType := some .uint256
    isInternal := true
    body := [Stmt.internalCallAssign ["tmp"] "recursiveNoRaw" [], Stmt.return (.literal 0)] }

private def constructorRecursiveNoRawCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body :=
      [Stmt.internalCallAssign ["tmp"] "recursiveNoRaw" [],
        Stmt.setStorage "value" (.localVar "tmp"),
        .stop] }

private def constructorRecursiveNoRawSpec : CompilationModel :=
  { name := "ConstructorRecursiveNoRaw"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorRecursiveNoRawCtor
    functions := [recursiveNoRawInternalHelper] }

private def constSevenInternalHelper : FunctionSpec :=
  { name := "constSeven"
    params := []
    returnType := some .uint256
    isInternal := true
    body := [Stmt.return (.literal 7)] }

private def helperFuelAlignSpec : CompilationModel :=
  { name := "HelperFuelAlign"
    fields := []
    constructor := none
    functions := [constSevenInternalHelper] }

private def helperCallerFunction : FunctionSpec :=
  { name := "callConstSeven"
    params := []
    returnType := some .uint256
    body :=
      [Stmt.internalCallAssign ["result"] "constSeven" []
      , Stmt.return (.param "result")] }

private def helperCallerTx : IRTransaction :=
  { sender := 4
    functionSelector := 0
    args := [] }

private def helperCallSpec : CompilationModel :=
  { name := "HelperCall"
    fields := []
    constructor := none
    functions := [constSevenInternalHelper, helperCallerFunction] }

private def helperFuelAlignRuntime : SourceSemantics.RuntimeState :=
  { world := Verity.defaultState
    bindings := []
    selector := 0 }

private def stopOnlyFunction : FunctionSpec :=
  { name := "stopOnly"
    params := []
    returnType := none
    body := [Stmt.stop] }

private def stopOnlySpec : CompilationModel :=
  { name := "StopOnly"
    fields := []
    constructor := none
    functions := [stopOnlyFunction] }

private def stopOnlyTx : IRTransaction :=
  { sender := 3
    functionSelector := 0
    args := [] }

private theorem literalMappingWrite_txNormalized :
    Function.TxContextNormalized literalMappingWriteTx := by
  simp [Function.TxContextNormalized, literalMappingWriteTx, Compiler.Constants.addressModulus,
    Compiler.Constants.evmModulus]

private theorem literalMappingWrite_calldataFits :
    Function.TxCalldataSizeFitsEvm literalMappingWriteTx := by
  simp [Function.TxCalldataSizeFitsEvm, literalMappingWriteTx, Compiler.Constants.evmModulus]

private theorem constructorOnly_txNormalized :
    Function.TxContextNormalized constructorOnlyTx := by
  simp [Function.TxContextNormalized, constructorOnlyTx, Compiler.Constants.addressModulus,
    Compiler.Constants.evmModulus]

private theorem constructorOnly_calldataFits :
    Function.TxCalldataSizeFitsEvm constructorOnlyTx := by
  simp [Function.TxCalldataSizeFitsEvm, constructorOnlyTx, Compiler.Constants.evmModulus]

private theorem constructorOnly_constructorCalldataFits :
    Function.TxConstructorCalldataSizeFitsEvm constructorOnlyTx := by
  simp [Function.TxConstructorCalldataSizeFitsEvm, constructorOnlyTx, Compiler.Constants.evmModulus]

example :
    FunctionBody.constructorRuntimeStateMatchesIR
      (SourceSemantics.effectiveFields constructorOnlySpec)
      { world := SourceSemantics.withConstructorTransactionContext Verity.defaultState constructorOnlyTx
        bindings := []
        selector := constructorOnlyTx.functionSelector }
      (FunctionBody.initialIRStateForTx constructorOnlySpec constructorOnlyTx Verity.defaultState) := by
  exact
    Function.initialIRStateForTx_matches_constructor_runtime
      constructorOnlySpec
      constructorOnlyTx
      Verity.defaultState
      constructorOnly_txNormalized
      constructorOnly_constructorCalldataFits

example :
    FunctionBody.constructorRuntimeStateMatchesIR
      (SourceSemantics.effectiveFields constructorOnlySpec)
      { world := SourceSemantics.withConstructorTransactionContext Verity.defaultState constructorOnlyTx
        bindings := []
        selector := constructorOnlyTx.functionSelector }
      (ParamLoading.applyBindingsToIRState
        (FunctionBody.initialIRStateForTx constructorOnlySpec constructorOnlyTx Verity.defaultState)
        [("initialOwner", Compiler.Constants.addressMask &&& 11)]) := by
  exact
    Function.initialIRStateForTx_matches_bound_constructor_runtime
      constructorOnlySpec
      constructorOnlyTx
      Verity.defaultState
      [("initialOwner", Compiler.Constants.addressMask &&& 11)]
      constructorOnly_txNormalized
      constructorOnly_constructorCalldataFits

private theorem constructorArg_txNormalized :
    Function.TxContextNormalized constructorArgTx := by
  simp [Function.TxContextNormalized, constructorArgTx, Compiler.Constants.addressModulus,
    Compiler.Constants.evmModulus]

private theorem constructorArg_calldataFits :
    Function.TxCalldataSizeFitsEvm constructorArgTx := by
  simp [Function.TxCalldataSizeFitsEvm, constructorArgTx, Compiler.Constants.evmModulus]

private theorem stopOnly_txNormalized :
    Function.TxContextNormalized stopOnlyTx := by
  simp [Function.TxContextNormalized, stopOnlyTx, Compiler.Constants.addressModulus,
    Compiler.Constants.evmModulus]

private theorem stopOnly_calldataFits :
    Function.TxCalldataSizeFitsEvm stopOnlyTx := by
  simp [Function.TxCalldataSizeFitsEvm, stopOnlyTx, Compiler.Constants.evmModulus]

private theorem constructorOnly_noConflict :
    firstFieldWriteSlotConflict constructorOnlySpec.fields = none := by
  native_decide

private theorem constructorOnly_compileBody_empty_surfaces_withFork :
    ∃ bodyStmts,
      compileStmtListWithFork
          constructorOnlySpec.fields
          []
          []
          .memory
          []
          false
          (constructorBodyScope constructorOnlyCtor.params)
          []
          Verity.Core.Intrinsics.HardFork.cancun
          constructorOnlyCtor.body =
        Except.ok bodyStmts := by
  have hhead :
      ∃ headIR,
        CompilationModel.compileStmt constructorOnlySpec.fields [] [] .memory [] false
          (constructorBodyScope constructorOnlyCtor.params) [] (Stmt.setStorageAddr "owner" (.param "initialOwner")) =
            Except.ok headIR := by
    refine ⟨
      match CompilationModel.compileStmt constructorOnlySpec.fields [] [] .memory [] false
          (constructorBodyScope constructorOnlyCtor.params) [] (Stmt.setStorageAddr "owner" (.param "initialOwner")) with
      | .ok headIR => headIR
      | .error _ => [], ?_⟩
    simp [constructorOnlySpec, constructorOnlyCtor, constructorOnlyOwnerField,
      CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      CompilationModel.compileSetStorage,
      CompilationModel.compileExprWithInternals, CompilationModel.isMapping,
      constructorOnly_owner_resolved_lit, Bind.bind, Except.bind, Pure.pure,
      Except.pure]
  have htail :
      ∃ tailIR,
        CompilationModel.compileStmtList constructorOnlySpec.fields [] [] .memory [] false
          (collectStmtBindNames (Stmt.setStorageAddr "owner" (.param "initialOwner")) ++
            (constructorBodyScope constructorOnlyCtor.params)) []
          [Stmt.stop] = Except.ok tailIR := by
    have hstop :
        ∃ stopIR,
          CompilationModel.compileStmt constructorOnlySpec.fields [] [] .memory [] false
            (collectStmtBindNames (Stmt.setStorageAddr "owner" (.param "initialOwner")) ++
              (constructorBodyScope constructorOnlyCtor.params)) [] Stmt.stop =
              Except.ok stopIR := by
      refine ⟨
        match CompilationModel.compileStmt constructorOnlySpec.fields [] [] .memory [] false
            (collectStmtBindNames (Stmt.setStorageAddr "owner" (.param "initialOwner")) ++
              (constructorBodyScope constructorOnlyCtor.params)) [] Stmt.stop with
        | .ok stopIR => stopIR
        | .error _ => [], ?_⟩
      simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        Pure.pure, Except.pure]
    rcases hstop with ⟨stopIR, hstop⟩
    exact ⟨stopIR ++ [],
      FunctionBody.compileStmtList_cons_eq_ok _ _ _ _ _ _ _ _ _ _ _ _
        hstop (FunctionBody.compileStmtList_nil_eq_ok _ _ _ _ _ _ _ _)⟩
  rcases hhead with ⟨headIR, hhead⟩
  rcases htail with ⟨tailIR, htail⟩
  exact ⟨headIR ++ tailIR,
    FunctionBody.compileStmtListWithFork_cons_eq_ok _ _ _ _ _ _ _ _ _ _ _ _ _ hhead htail⟩

private theorem constructorOnly_compileBody :
    ∃ bodyStmts,
      compileStmtList
          constructorOnlySpec.fields
          constructorOnlySpec.events
          constructorOnlySpec.errors
          .memory
          []
          false
          (constructorBodyScope constructorOnlyCtor.params)
          []
          constructorOnlyCtor.body [] =
        Except.ok bodyStmts := by
  refine ⟨
    match compileStmtList
        constructorOnlySpec.fields
        constructorOnlySpec.events
        constructorOnlySpec.errors
        .memory
        []
        false
        (constructorBodyScope constructorOnlyCtor.params)
        []
        constructorOnlyCtor.body [] with
     | .ok body => body
     | .error _ => [], ?_⟩
  rcases constructorOnly_compileBody_empty_surfaces_withFork with ⟨body, hbody⟩
  rw [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList] at hbody
  simp [constructorOnlySpec, constructorOnlyCtor] at hbody
  simp [constructorOnlySpec, constructorOnlyCtor]
  rw [hbody]

private theorem constructorOnly_compileConstructor :
    ∃ bodyStmts,
      compileConstructor
          constructorOnlySpec.fields
          constructorOnlySpec.events
          constructorOnlySpec.errors
          []
      constructorOnlySpec.constructor =
    Except.ok (genConstructorArgLoads constructorOnlyCtor.params ++ bodyStmts) ∧
      compileStmtList
          constructorOnlySpec.fields
          constructorOnlySpec.events
          constructorOnlySpec.errors
          .memory
          []
          false
          (constructorBodyScope constructorOnlyCtor.params)
          []
          constructorOnlyCtor.body [] =
        Except.ok bodyStmts := by
  rcases constructorOnly_compileBody with ⟨bodyStmts, hbodyCompile⟩
  rcases Function.compileConstructor_ok_components
      constructorOnlySpec.fields
      constructorOnlySpec.events
      constructorOnlySpec.errors
      constructorOnlyCtor
      (genConstructorArgLoads constructorOnlyCtor.params ++ bodyStmts)
      (by
        simp [CompilationModel.compileConstructor,
          FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
          hbodyCompile, Bind.bind, Except.bind, Pure.pure, Except.pure]) with
      ⟨_, _, hdeploy⟩
  refine ⟨bodyStmts, ?_, hbodyCompile⟩
  exact Function.compileConstructor_some_ok_of_body
    constructorOnlySpec.fields
    constructorOnlySpec.events
    constructorOnlySpec.errors
    constructorOnlyCtor
    bodyStmts
    hbodyCompile

example :
    ∃ bodyStmts,
      compileConstructor
          constructorOnlySpec.fields
          constructorOnlySpec.events
          constructorOnlySpec.errors
          []
          constructorOnlySpec.constructor =
        Except.ok (genConstructorArgLoads constructorOnlyCtor.params ++ bodyStmts) := by
  rcases constructorOnly_compileConstructor with ⟨bodyStmts, hdeploy, _⟩
  exact ⟨bodyStmts, hdeploy⟩

example :
    ∀ returns retNames bodyStmts,
      validateFunctionSpec identityInternalHelper = Except.ok () →
      functionReturns identityInternalHelper = Except.ok returns →
      retNames =
        freshInternalRetNames returns
          (internalFunctionYulParamNames identityInternalHelper.params ++
            collectStmtListBindNames identityInternalHelper.body) →
      compileStmtList [] [] [] .calldata retNames true
        (internalFunctionYulParamNames identityInternalHelper.params ++ retNames)
        []
        identityInternalHelper.body = Except.ok bodyStmts →
      compileInternalFunction [] [] [] [] identityInternalHelper =
        Except.ok
          (YulStmt.funcDef
            (internalFunctionYulName identityInternalHelper.name)
            (internalFunctionYulParamNames identityInternalHelper.params)
            retNames
            bodyStmts) := by
  intro returns retNames bodyStmts hvalidate hreturns hretNames hbody
  exact compileInternalFunction_some_ok_of_components
    [] [] [] identityInternalHelper returns retNames bodyStmts
    hvalidate hreturns hretNames hbody

example :
    (SourceSemantics.interpretInternalFunctionFuel
      helperFuelAlignSpec
      0
      constSevenInternalHelper
      Verity.defaultState
      []).returnValue = some 7 := by
  native_decide

example :
    (SourceSemantics.interpretFunctionWithHelpers
      helperCallSpec
      1
      helperCallerFunction
      helperCallerTx
      Verity.defaultState).returnValue = some 7 := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorArgSpec
      constructorArgCtor
      constructorArgTx
      Verity.defaultState).success = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorArgSpec
      constructorArgCtor
      constructorArgTx
      Verity.defaultState).finalStorage 0 = 13 := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorArgSpec
      0
      constructorArgCtor
      constructorArgTx
      Verity.defaultState).success = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorArgSpec
      0
      constructorArgCtor
      constructorArgTx
      Verity.defaultState).finalStorage 0 = 13 := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorArgSpec
      constructorArgCtor
      constructorArgTrailingTx
      Verity.defaultState).success = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorArgSpec
      constructorArgCtor
      constructorArgTrailingTx
      Verity.defaultState).finalStorage 0 = 13 := by
  native_decide

example :
    SourceSemantics.constructorExecutionBindings
      constructorHelperArgCtor
      constructorHelperArgTx.args =
      some [("arg0", 17), ("initialValue", 17)] := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorHelperArgSpec
      1
      constructorHelperArgCtor
      constructorHelperArgTx
      Verity.defaultState).success = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorHelperArgSpec
      1
      constructorHelperArgCtor
      constructorHelperArgTx
      Verity.defaultState).finalStorage 0 = 17 := by
  native_decide

example :
    SourceSemantics.directHelperTouchesUnsupportedConstructorRawCalldataSurface
      constructorHelperRawCalldataSpec
      (constructorAsFunctionSpec constructorHelperRawCalldataCtor) = true := by
  native_decide

example :
    SourceSemantics.helperClosureTouchesUnsupportedConstructorRawCalldataSurface
      constructorNestedHelperRawCalldataSpec
      (constructorNestedHelperRawCalldataSpec.functions.length + 1)
      (constructorAsFunctionSpec constructorNestedHelperRawCalldataCtor) = true := by
  native_decide

example :
    SourceSemantics.helperClosureTouchesUnsupportedConstructorRawCalldataSurface
      constructorRecursiveNoRawSpec
      (constructorRecursiveNoRawSpec.functions.length + 1)
      (constructorAsFunctionSpec constructorRecursiveNoRawCtor) = false := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorHelperRawCalldataSpec
      1
      constructorHelperRawCalldataCtor
      constructorHelperArgTx
      Verity.defaultState).success = false := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorNestedHelperRawCalldataSpec
      2
      constructorNestedHelperRawCalldataCtor
      constructorHelperArgTx
      Verity.defaultState).success = false := by
  native_decide

example :
    stmtListTouchesUnsupportedConstructorRawCalldataSurface constructorCalldataCtor.body = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorCalldataSpec
      constructorCalldataCtor
      constructorCalldataTx
      Verity.defaultState).success = false := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorCalldataSpec
      0
      constructorCalldataCtor
      constructorCalldataTx
      Verity.defaultState).success = false := by
  native_decide

example :
    stmtListTouchesUnsupportedConstructorRawCalldataSurface constructorRightCalldataCtor.body = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorRightCalldataSpec
      constructorRightCalldataCtor
      constructorCalldataTx
      Verity.defaultState).success = false := by
  native_decide

example :
    stmtListTouchesUnsupportedConstructorRawCalldataSurface constructorRightCalldataloadCtor.body = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorRightCalldataloadSpec
      0
      constructorRightCalldataloadCtor
      constructorCalldataTx
      Verity.defaultState).success = false := by
  native_decide

example
    (ir : IRContract)
    (hcompile : CompilationModel.compile literalMappingWriteSpec [literalMappingWriteSelector] = Except.ok ir)
    (hbodySafety :
      ∀ stmt ∈ literalMappingWriteFunction.body,
        StmtMappingWriteSlotSafe literalMappingWriteSpec.fields stmt) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsExceptMappingWrites
        literalMappingWriteSpec
        [literalMappingWriteSelector]
        literalMappingWrite_supported_spec
        literalMappingWriteTx
        Verity.defaultState)
      (interpretIR
        ir
        literalMappingWriteTx
        (FunctionBody.initialIRStateForTx
          literalMappingWriteSpec
          literalMappingWriteTx
          Verity.defaultState)) := by
  exact Contract.compile_preserves_semantics_except_mapping_writes_stmtSafety
    (model := literalMappingWriteSpec)
    (selectors := [literalMappingWriteSelector])
    (hSupported := literalMappingWrite_supported_spec)
    (ir := ir)
    (tx := literalMappingWriteTx)
    (initialWorld := Verity.defaultState)
    (hnoConflict := literalMappingWrite_noConflict)
    (hsafety := by
      intro fn hfn
      simp [selectorDispatchedFunctions, literalMappingWriteSpec, literalMappingWriteFunction] at hfn
      rcases hfn with ⟨rfl, _, _⟩
      exact hbodySafety)
    (htxNormalized := literalMappingWrite_txNormalized)
    (hcalldataSizeFits := literalMappingWrite_calldataFits)
    (hcompile := hcompile)

example :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretConstructorWithHelpers
        constructorOnlySpec
        0
        constructorOnlyCtor
        constructorOnlyTx
        Verity.defaultState)
      (Function.execResultToIRResult
        (FunctionBody.initialIRStateForTx constructorOnlySpec constructorOnlyTx Verity.defaultState)
        (execIRStmts
          (sizeOf
            (match compileStmtList
                constructorOnlySpec.fields [] [] .memory [] false
                (constructorBodyScope constructorOnlyCtor.params)
                []
                [Stmt.setStorageAddr "owner" (.param "initialOwner"), .stop] [] with
             | .ok body => body
             | .error _ => []) + 1)
          (ParamLoading.applyBindingsToIRState
            (FunctionBody.initialIRStateForTx constructorOnlySpec constructorOnlyTx Verity.defaultState)
            [("arg0", Compiler.Constants.addressMask &&& 11),
              ("initialOwner", Compiler.Constants.addressMask &&& 11)])
          (match compileStmtList
              constructorOnlySpec.fields [] [] .memory [] false
              (constructorBodyScope constructorOnlyCtor.params)
              []
              [Stmt.setStorageAddr "owner" (.param "initialOwner"), .stop] [] with
           | .ok body => body
           | .error _ => []))) := by
  have hbodyCompile :
      compileStmtList constructorOnlySpec.fields constructorOnlySpec.events constructorOnlySpec.errors
        .memory [] false (constructorBodyScope constructorOnlyCtor.params) [] constructorOnlyCtor.body [] =
      Except.ok
        (match compileStmtList constructorOnlySpec.fields [] [] .memory [] false
            (constructorBodyScope constructorOnlyCtor.params) [] constructorOnlyCtor.body [] with
         | .ok body => body
         | .error _ => []) := by
    rcases constructorOnly_compileBody_empty_surfaces_withFork with ⟨body, hbody⟩
    rw [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList] at hbody
    simp [constructorOnlySpec, constructorOnlyCtor] at hbody
    simp [constructorOnlySpec, constructorOnlyCtor]
    rw [hbody]
  have hbind :
      SourceSemantics.bindSupportedParams
        [{ name := "initialOwner", ty := .address }]
        constructorOnlyTx.args =
      some [("initialOwner", Compiler.Constants.addressMask &&& 11)] := by
    native_decide
  have hconstructorBindings :
      SourceSemantics.constructorExecutionBindings
        constructorOnlyCtor
        constructorOnlyTx.args =
      some [("arg0", Compiler.Constants.addressMask &&& 11),
        ("initialOwner", Compiler.Constants.addressMask &&& 11)] := by
    native_decide
  simpa [constructorOnlySpec, constructorOnlyTx, constructorOnlySupported, Function.execResultToIRResult] using
    Function.supported_constructor_body_correct_with_body_interface
      (model := constructorOnlySpec)
      (ctor := constructorOnlyCtor)
      (helperFuel := 0)
      (hnormalized := rfl)
      (hfunctionNamesNodup := by decide)
      (hSupported := constructorOnlySupported)
      (hnoConflict := constructorOnly_noConflict)
      (hsafety := by
        intro stmt hmem
        simp [constructorOnlyCtor] at hmem
        rcases hmem with rfl | rfl
        · simp [StmtMappingWriteSlotSafe]
        · simp [StmtMappingWriteSlotSafe])
      (hnoEvents := rfl)
      (hnoErrors := rfl)
      (tx := constructorOnlyTx)
      (initialWorld := Verity.defaultState)
      (bindings := [("initialOwner", Compiler.Constants.addressMask &&& 11)])
      (ctorBindings := [("arg0", Compiler.Constants.addressMask &&& 11),
        ("initialOwner", Compiler.Constants.addressMask &&& 11)])
      (bodyStmts := match compileStmtList constructorOnlySpec.fields [] [] .memory [] false
          (constructorBodyScope constructorOnlyCtor.params) [] constructorOnlyCtor.body [] with
        | .ok body => body
        | .error _ => [])
      (hbodyCompile := hbodyCompile)
      (hbind := hbind)
      (hconstructorBindings := hconstructorBindings)
      (htxNormalized := constructorOnly_txNormalized)
      (hcalldataSizeFits := constructorOnly_constructorCalldataFits)

example :
    ∃ bodyStmts bindings,
      SourceSemantics.constructorExecutionBindings
          constructorOnlyCtor
          constructorOnlyTrailingTx.args =
        some bindings ∧
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretConstructorWithHelpers
          constructorOnlySpec 0 constructorOnlyCtor constructorOnlyTrailingTx Verity.defaultState)
        (Function.execResultToIRResult
          (FunctionBody.initialIRStateForTx constructorOnlySpec constructorOnlyTrailingTx
            Verity.defaultState)
          (execIRStmts
            (sizeOf bodyStmts + 1)
            (ParamLoading.applyBindingsToIRState
              (FunctionBody.initialIRStateForTx constructorOnlySpec constructorOnlyTrailingTx
                Verity.defaultState)
              bindings)
            bodyStmts)) := by
  let bodyStmts :=
    match compileStmtList constructorOnlySpec.fields [] [] .memory [] false
        (constructorBodyScope constructorOnlyCtor.params) [] constructorOnlyCtor.body [] with
    | .ok body => body
    | .error _ => []
  let bindings := [("arg0", Compiler.Constants.addressMask &&& 11),
    ("initialOwner", Compiler.Constants.addressMask &&& 11)]
  refine ⟨bodyStmts, bindings, ?_, ?_⟩
  · native_decide
  · have hbodyCompile :
        compileStmtList constructorOnlySpec.fields constructorOnlySpec.events constructorOnlySpec.errors
          .memory [] false (constructorBodyScope constructorOnlyCtor.params) [] constructorOnlyCtor.body [] =
        Except.ok bodyStmts := by
      rcases constructorOnly_compileBody_empty_surfaces_withFork with ⟨body, hbody⟩
      rw [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList] at hbody
      simp [constructorOnlySpec, constructorOnlyCtor] at hbody
      simp [bodyStmts, constructorOnlySpec, constructorOnlyCtor]
      rw [hbody]
    have hbindParams :
        SourceSemantics.bindSupportedParams constructorOnlyCtor.params
            (constructorOnlyTrailingTx.args.take constructorOnlyCtor.params.length) =
          some [("initialOwner", Compiler.Constants.addressMask &&& 11)] := by
      native_decide
    have hconstructorBindings :
        SourceSemantics.constructorExecutionBindings constructorOnlyCtor constructorOnlyTrailingTx.args =
          some bindings := by
      native_decide
    simpa [constructorOnlySpec, constructorOnlyTrailingTx, constructorOnlyTx, constructorOnlySupported,
      Function.execResultToIRResult] using
      Function.supported_constructor_body_correct_with_body_interface
        (model := constructorOnlySpec)
        (ctor := constructorOnlyCtor)
        (helperFuel := 0)
        (hnormalized := rfl)
        (hfunctionNamesNodup := by decide)
        (hSupported := constructorOnlySupported)
        (hnoConflict := constructorOnly_noConflict)
        (hsafety := by
          intro stmt hmem
          simp [constructorOnlyCtor] at hmem
          rcases hmem with rfl | rfl
          · simp [StmtMappingWriteSlotSafe]
          · simp [StmtMappingWriteSlotSafe])
        (hnoEvents := rfl)
        (hnoErrors := rfl)
        (tx := constructorOnlyTrailingTx)
        (initialWorld := Verity.defaultState)
        (bindings := [("initialOwner", Compiler.Constants.addressMask &&& 11)])
        (ctorBindings := bindings)
        (bodyStmts := bodyStmts)
        (hbodyCompile := hbodyCompile)
        (hbind := hbindParams)
        (hconstructorBindings := hconstructorBindings)
        (htxNormalized := by
          simp [Function.TxContextNormalized, constructorOnlyTrailingTx, constructorOnlyTx,
            Compiler.Constants.addressModulus, Compiler.Constants.evmModulus])
        (hcalldataSizeFits := by
          simp [Function.TxConstructorCalldataSizeFitsEvm, constructorOnlyTrailingTx,
            constructorOnlyTx, Compiler.Constants.evmModulus])

example :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers
        stopOnlySpec
        1
        stopOnlyFunction
        stopOnlyTx
        Verity.defaultState)
      (FunctionBody.irResultOfExecResultWithInternals
        (FunctionBody.initialIRStateForTx stopOnlySpec stopOnlyTx Verity.defaultState)
        (.stop (FunctionBody.initialIRStateForTx stopOnlySpec stopOnlyTx Verity.defaultState))) := by
  have hbind :
      SourceSemantics.bindSupportedParams stopOnlyFunction.params stopOnlyTx.args = some [] := by
    rfl
  have hsource :
      SourceSemantics.execStmtListWithHelpers stopOnlySpec (SourceSemantics.effectiveFields stopOnlySpec)
        1
        { world := SourceSemantics.withTransactionContext Verity.defaultState stopOnlyTx
          bindings := []
          selector := stopOnlyTx.functionSelector }
        stopOnlyFunction.body =
      .stop
        { world := SourceSemantics.withTransactionContext Verity.defaultState stopOnlyTx
          bindings := []
          selector := stopOnlyTx.functionSelector } := by
    simp [stopOnlyFunction, SourceSemantics.execStmtListWithHelpers,
      SourceSemantics.execStmtWithHelpers]
  have hstate :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields stopOnlySpec)
        { world := SourceSemantics.withTransactionContext Verity.defaultState stopOnlyTx
          bindings := []
          selector := stopOnlyTx.functionSelector }
        (FunctionBody.initialIRStateForTx stopOnlySpec stopOnlyTx Verity.defaultState) := by
    simpa using
      Function.initialIRStateForTx_matches_runtime
        stopOnlySpec
        stopOnlyTx
        Verity.defaultState
        stopOnly_txNormalized
        stopOnly_calldataFits
  exact
    Function.interpretFunctionWithHelpers_eq_execResultToIRResultWithInternals_of_body
      (model := stopOnlySpec)
      (fn := stopOnlyFunction)
      (helperFuel := 1)
      (tx := stopOnlyTx)
      (initialWorld := Verity.defaultState)
      (sourceResult := .stop
        { world := SourceSemantics.withTransactionContext Verity.defaultState stopOnlyTx
          bindings := []
          selector := stopOnlyTx.functionSelector })
      (rollback := FunctionBody.initialIRStateForTx stopOnlySpec stopOnlyTx Verity.defaultState)
      (irResult := .stop (FunctionBody.initialIRStateForTx stopOnlySpec stopOnlyTx Verity.defaultState))
      (bindings := [])
      (hbind := hbind)
      (hsource := hsource)
      (hrollbackStorage := by simp [FunctionBody.initialIRStateForTx, stopOnlySpec, stopOnlyTx])
      (hrollbackEvents := by simp [FunctionBody.initialIRStateForTx, stopOnlySpec, stopOnlyTx])
      (hmatch := hstate)

private def eventTrackingSpec : CompilationModel :=
  { name := "EventTracking"
    fields := []
    constructor := none
    events := [
      { name := "Evt"
        params := [
          { name := "topic", ty := .uint256, kind := .indexed },
          { name := "value", ty := .uint256, kind := .unindexed }
        ] }
    ]
    functions := [] }

private def eventTrackingRuntime : SourceSemantics.RuntimeState :=
  { world := Verity.defaultState
    bindings := []
    selector := 0 }

example :
    SourceSemantics.execStmtWithHelpers eventTrackingSpec [] 0 eventTrackingRuntime
      (.emit "Evt" [.literal 11, .literal 22]) =
    match SourceSemantics.eventScratchMemoryAfterEmit?
        eventTrackingSpec.events "Evt"
        [11 % Compiler.Constants.evmModulus, 22 % Compiler.Constants.evmModulus]
        eventTrackingRuntime.world.memory with
    | some memory =>
        .continue
          { eventTrackingRuntime with
            world := { eventTrackingRuntime.world with
                memory := memory
                events := eventTrackingRuntime.world.events ++
                  [{ name := "Evt"
                     args := [Verity.Core.Uint256.ofNat (22 % Compiler.Constants.evmModulus)]
                     indexedArgs := [
                       Verity.Core.Uint256.ofNat
                         (SourceSemantics.eventSignatureTopic
                           { name := "Evt"
                             params := [
                               { name := "topic", ty := .uint256, kind := .indexed },
                               { name := "value", ty := .uint256, kind := .unindexed }
                             ] }),
                       Verity.Core.Uint256.ofNat (11 % Compiler.Constants.evmModulus)] }] } }
    | none => .revert := by
  have hunindexed :
      (EventParamKind.unindexed == EventParamKind.indexed) = false := by
    native_decide
  have hindexed :
      (EventParamKind.indexed == EventParamKind.indexed) = true := by
    native_decide
  generalize hscratch :
      SourceSemantics.eventScratchMemoryAfterEmit?
        [{ name := "Evt"
           params := [
             { name := "topic", ty := .uint256, kind := .indexed },
             { name := "value", ty := .uint256, kind := .unindexed }
           ] }]
        "Evt"
        [11 % Compiler.Constants.evmModulus, 22 % Compiler.Constants.evmModulus]
        Verity.defaultState.memory = scratch
  cases scratch <;>
  simp [eventTrackingSpec, eventTrackingRuntime, SourceSemantics.execStmtWithHelpers,
    SourceSemantics.evalExprListWithHelpers, SourceSemantics.evalExprWithHelpers,
    SourceSemantics.eventFromResolvedArgs?, SourceSemantics.splitEventArgsByParams,
    SourceSemantics.normalizeEventValue, hscratch,
    hunindexed, hindexed]

private def eventNormalizationSpec : CompilationModel :=
  { name := "EventNormalization"
    fields := []
    constructor := none
    events := [
      { name := "Evt"
        params := [
          { name := "flag", ty := .bool, kind := .indexed },
          { name := "owner", ty := .address, kind := .unindexed },
          { name := "small", ty := .uint8, kind := .unindexed }
        ] }
    ]
    functions := [] }

example :
    SourceSemantics.eventFromResolvedArgs? eventNormalizationSpec.events "Evt"
      [2, Compiler.Constants.addressMask + 18, 300] =
    some
      { name := "Evt"
        args := [
          Verity.Core.Uint256.ofNat 17,
          Verity.Core.Uint256.ofNat 44
        ]
        indexedArgs := [
          Verity.Core.Uint256.ofNat
            (SourceSemantics.eventSignatureTopic
              { name := "Evt"
                params := [
                  { name := "flag", ty := .bool, kind := .indexed },
                  { name := "owner", ty := .address, kind := .unindexed },
                  { name := "small", ty := .uint8, kind := .unindexed }
                ] }),
          Verity.Core.Uint256.ofNat 1] } := by
  have hunindexed :
      (EventParamKind.unindexed == EventParamKind.indexed) = false := by
    native_decide
  have hindexed :
      (EventParamKind.indexed == EventParamKind.indexed) = true := by
    native_decide
  simp [eventNormalizationSpec, SourceSemantics.eventFromResolvedArgs?,
    SourceSemantics.splitEventArgsByParams, SourceSemantics.normalizeEventValue,
    SourceSemantics.wordNormalize, SourceSemantics.uint8Modulus,
    Compiler.Constants.addressMask, Compiler.Constants.evmModulus,
    Verity.Core.Uint256.ofNat, hunindexed, hindexed]

private def scalarEventSmokeFunction : FunctionSpec :=
  { name := "ping"
    params := []
    returnType := none
    body := [Stmt.emit "Ping" [.literal 7, .literal 9]] }

private def scalarEventSmokeSpec : CompilationModel :=
  { name := "ScalarEventSmoke"
    fields := []
    constructor := none
    events :=
      [{ name := "Ping"
         params :=
          [{ name := "topic", ty := .uint256, kind := .indexed },
           { name := "value", ty := .uint256, kind := .unindexed }] }]
    functions := [scalarEventSmokeFunction] }

private def scalarEventSmokeSelector : Nat := 0x22222222

private theorem scalarEventSmoke_compileEmit_empty_events_ne_ok
    (compiledIR : List YulStmt) :
    compileEmit [] [] .calldata "Ping" [Expr.literal 7, Expr.literal 9] ≠
      Except.ok compiledIR := by
  simp [compileEmit, bind, Except.bind]

private theorem scalarEventSmoke_noPackedFields :
    ∀ field ∈ scalarEventSmokeSpec.fields, field.packedBits = none := by
  intro field hfield
  simp [scalarEventSmokeSpec] at hfield

private theorem scalarEventSmoke_noFallback :
    ∀ fn ∈ scalarEventSmokeSpec.functions, fn.name != "fallback" := by
  intro fn hfn
  simp [scalarEventSmokeSpec, scalarEventSmokeFunction] at hfn
  rcases hfn with rfl
  decide

private theorem scalarEventSmoke_noReceive :
    ∀ fn ∈ scalarEventSmokeSpec.functions, fn.name != "receive" := by
  intro fn hfn
  simp [scalarEventSmokeSpec, scalarEventSmokeFunction] at hfn
  rcases hfn with rfl
  decide

private def scalarEventSmoke_supported_function :
    ∀ fn, fn ∈ scalarEventSmokeSpec.functions →
      SupportedFunctionWithScalarEvents scalarEventSmokeSpec fn := by
  intro fn hfn
  simp [scalarEventSmokeSpec, scalarEventSmokeFunction] at hfn
  rcases hfn with rfl
  exact
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      noNonReentrant := rfl
      params :=
        { namesNodup := by decide
          supported := by intro param hparam; cases hparam
          calldataThreshold := by decide }
      returns := { resolved := ⟨[], rfl, trivial⟩ }
      body :=
        { stmtList :=
            .emitEvent
              (by intro arg harg; simp at harg; rcases harg with rfl | rfl <;> exact .literal _)
              (by
                intro arg harg
                simp at harg
                rcases harg with rfl | rfl
                · intro name hname; simp [FunctionBody.exprBoundNames] at hname
                · intro name hname; simp [FunctionBody.exprBoundNames] at hname)
          core := { surfaceClosed := by decide }
          state := { surfaceClosed := by decide }
          calls :=
            { helpers :=
                { helperRank := 1
                  callNamesNodup := helperCallNames_nodup _
                  summaryOf := by
                    intro calleeName hmem
                    simp [helperCallNames, stmtListInternalHelperCallNames,
                      stmtInternalHelperCallNames, exprListInternalHelperCallNames,
                      exprInternalHelperCallNames] at hmem
                  calleeRanksDecrease := by
                    intro calleeName hmem
                    simp [helperCallNames, stmtListInternalHelperCallNames,
                      stmtInternalHelperCallNames, exprListInternalHelperCallNames,
                      exprInternalHelperCallNames] at hmem
                  exprCallsPreserveWorld := by
                    intro calleeName hmem
                    simp [exprHelperCallNames, stmtListExprHelperCallNames,
                      stmtExprHelperCallNames, exprListInternalHelperCallNames,
                      exprInternalHelperCallNames] at hmem }
              foreign := by decide
              lowLevel := by decide }
          contractSurfaceWithEvents := by decide
          topLevelEventHeads := by
            intro s hs
            simp at hs
            rcases hs with rfl
            exact Or.inl rfl
          eventScratchFreshInitial := by decide
          eventScratchFreshStmts := by
            intro s hs
            simp at hs
            rcases hs with rfl
            simp [collectStmtBindNames]
          emitArgsInScope := by
            intro s hs eventName args heq arg harg
            simp at hs
            rcases hs with rfl
            cases heq
            simp at harg
            rcases harg with rfl | rfl
            · intro name hname; simp [FunctionBody.exprBoundNames] at hname
            · intro name hname; simp [FunctionBody.exprBoundNames] at hname
          noLocalObligations := rfl } }

private def scalarEventSmoke_supported_spec :
    SupportedSpecWithScalarEvents scalarEventSmokeSpec [scalarEventSmokeSelector] :=
  { invariants :=
      { normalizedFields := rfl
        noPackedFields := scalarEventSmoke_noPackedFields
        selectorCount := by decide
        selectorsDistinct := by decide
        functionNamesNodup := by decide }
    surface :=
      { eventsSupported := by intro eventDef hmem; simp [scalarEventSmokeSpec] at hmem; rcases hmem with rfl; decide
        noErrors := rfl
        noExternals := rfl
        noAdtTypes := rfl
        noCheckedArithmetic := by
          simp [contractUsesCheckedArithmetic, scalarEventSmokeSpec,
            scalarEventSmokeFunction, stmtListMayUseCheckedArithmetic,
            stmtMayUseCheckedArithmetic]
        noTemplateIntrinsics := by
          rw [templateIntrinsicItems, scalarEventSmokeSpec, scalarEventSmokeFunction]
          unfold collectTemplateIntrinsicsFromStmts
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [collectTemplateIntrinsicsFromStmt.eq_def]
          simp only [Stmt.directMetadata, Stmt.childLists, List.attach_nil,
            List.flatMap_nil, List.append_nil]
          simp only [List.flatMap_cons, List.flatMap_nil]
          rw [collectTemplateIntrinsicsFromExpr.eq_def]
          rw [collectTemplateIntrinsicsFromExpr.eq_def]
          simp [Expr.children]
        noFallback := scalarEventSmoke_noFallback
        noReceive := scalarEventSmoke_noReceive }
    constructor := by
      intro ctor hctor
      simp [scalarEventSmokeSpec] at hctor
    functions := scalarEventSmoke_supported_function }

private theorem scalarEventSmoke_helperFree :
    ∀ fn, fn ∈ selectorDispatchedFunctions scalarEventSmokeSpec →
      StmtListHelperFreeNonEventStepInterface
        (SourceSemantics.effectiveFields scalarEventSmokeSpec)
        (fn.params.map (·.name)) fn.body := by
  intro fn hfn
  simp [scalarEventSmokeSpec, selectorDispatchedFunctions, scalarEventSmokeFunction] at hfn
  rcases hfn with ⟨rfl, _hinternal, _hspecial⟩
  exact .cons
    (fun _hhelper hevent => by simp [stmtTouchesEventSurface] at hevent)
    .nil

private theorem scalarEventSmoke_disjoint
    (ir : IRContract) :
    ∀ fn, fn ∈ selectorDispatchedFunctions scalarEventSmokeSpec →
      StmtListHelperFreeCompiledCallsDisjoint { ir with internalFunctions := [] }
        (SourceSemantics.effectiveFields scalarEventSmokeSpec)
        (fn.params.map (·.name)) fn.body := by
  intro fn hfn
  simp [scalarEventSmokeSpec, selectorDispatchedFunctions, scalarEventSmokeFunction] at hfn
  rcases hfn with ⟨rfl, _hinternal, _hspecial⟩
  exact .cons
    (fun _hhelper compiledIR hcompile => by
      have hbad := scalarEventSmoke_compileEmit_empty_events_ne_ok compiledIR
      simp [SourceSemantics.effectiveFields, scalarEventSmokeSpec,
        CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
      exact False.elim (hbad hcompile))
    .nil

theorem scalarEventSmoke_compile_preserves_semantics_with_scalar_events
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile :
      CompilationModel.compile scalarEventSmokeSpec [scalarEventSmokeSelector] =
        Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsWithScalarEvents scalarEventSmokeSpec
        [scalarEventSmokeSelector] scalarEventSmoke_supported_spec tx initialWorld)
      (interpretIR ir tx
        (FunctionBody.initialIRStateForTx scalarEventSmokeSpec tx initialWorld)) := by
  exact Contract.compile_preserves_semantics_with_scalar_events
    (model := scalarEventSmokeSpec)
    (selectors := [scalarEventSmokeSelector])
    (hSupported := scalarEventSmoke_supported_spec)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)
    (hcompile := hcompile)
    (hfuelPos := by
      dsimp [SupportedSpecWithScalarEvents.helperFuel,
        SupportedSpecWithScalarEvents.helperFuelOfFunction,
        scalarEventSmoke_supported_spec, scalarEventSmokeSpec,
        selectorDispatchedFunctions, SupportedFunctionWithScalarEvents.helperFuel,
        SupportedSpecWithScalarEvents.supportedFunctionOfSelectorDispatched,
        scalarEventSmoke_supported_function]
      simp [scalarEventSmokeFunction, isInteropEntrypointName])
    (hhelperFree := scalarEventSmoke_helperFree)
    (hstmtDisjoint := scalarEventSmoke_disjoint ir)

end Compiler.Proofs.IRGeneration.ContractFeatureTest
