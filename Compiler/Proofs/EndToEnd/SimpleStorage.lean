import Compiler.Proofs.EndToEnd.Base

namespace Compiler.Proofs.EndToEnd

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends

/-! ## Concrete Instantiation: SimpleStorage -/

/-- The concrete SimpleStorage IR fixture uses only EVMYulLean-bridged Yul
shapes: calldata parameter loading, one literal-slot storage write, one memory
write from `sload`, and `stop`/`return` terminators. -/
private theorem simpleStorage_functions_bridged :
    ∀ fn, fn ∈ simpleStorageIRContract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body := by
  intro fn hmem
  simp [simpleStorageIRContract] at hmem
  rcases hmem with rfl | rfl
  · apply Compiler.Proofs.YulGeneration.Backends.BridgedStmts_cons_let
    · exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.call
        "calldataload" [Yul.YulExpr.lit 4]
        (by
          left
          simp [Compiler.Proofs.YulGeneration.Backends.bridgedBuiltins])
        (by
          intro arg harg
          simp at harg
          subst arg
          exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit 4)
    · apply Compiler.Proofs.YulGeneration.Backends.BridgedStmts_cons_sstore_lit
      · exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.ident "value"
      · exact Compiler.Proofs.YulGeneration.Backends.BridgedStmts_singleton_stop
  · apply Compiler.Proofs.YulGeneration.Backends.BridgedStmts_cons_mstore
    · exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit 0
    · exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.call
        "sload" [Yul.YulExpr.lit 0]
        (by
          left
          simp [Compiler.Proofs.YulGeneration.Backends.bridgedBuiltins])
        (by
          intro arg harg
          simp at harg
          subst arg
          exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit 0)
    · exact Compiler.Proofs.YulGeneration.Backends.BridgedStmts_singleton_return
        (Yul.YulExpr.lit 0) (Yul.YulExpr.lit 32)
        (Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit 0)
        (Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit 32)

private theorem simpleStorage_functions_loop_free :
    ∀ fn, fn ∈ simpleStorageIRContract.functions →
      yulStmtsLoopFree fn.body = true := by
  intro fn hmem
  simp [simpleStorageIRContract] at hmem ⊢
  rcases hmem with rfl | rfl <;> rfl

/-- The emitted SimpleStorage runtime consists of the single generated external
dispatcher shell for the two concrete SimpleStorage functions.

This pins down the outer runtime layer that the native dispatcher bridge must
peel before applying the concrete lowered selector-switch lemmas. -/
private theorem simpleStorage_runtimeCode_eq_single_dispatcher :
    (Compiler.emitYul simpleStorageIRContract).runtimeCode =
      [Compiler.CodegenCommon.initFreeMemoryPointer,
        Compiler.CodegenCommon.buildSwitch
        simpleStorageIRContract.functions none none] := by
  dsimp [Compiler.emitYul, Compiler.CodegenCommon.emitYul,
    Compiler.runtimeCode, Compiler.CodegenCommon.runtimeCode,
    simpleStorageIRContract]

private abbrev simpleStorageBuildSwitchSourceCases : List (Nat × List Yul.YulStmt) :=
  simpleStorageIRContract.functions.map (fun fn =>
    (fn.selector,
      Compiler.CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
        ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++ fn.body)))

private abbrev simpleStorageBuildSwitchBody : List Yul.YulStmt :=
  [Yul.YulStmt.let_ "__has_selector"
    (Yul.YulExpr.call "iszero"
      [Yul.YulExpr.call "lt"
        [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]),
   Yul.YulStmt.if_ (Yul.YulExpr.call "iszero"
      [Yul.YulExpr.ident "__has_selector"])
      (Compiler.CodegenCommon.defaultDispatchCase none none),
   Yul.YulStmt.if_ (Yul.YulExpr.ident "__has_selector")
      [Yul.YulStmt.switch
        (Yul.YulExpr.call "shr"
          [Yul.YulExpr.lit Compiler.Constants.selectorShift,
           Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
        simpleStorageBuildSwitchSourceCases
        (some (Compiler.CodegenCommon.defaultDispatchCase none none))]]

private theorem lowerRuntimeContractNative_single_stmt_eq_lowerStmtsNative
    (stmt : Yul.YulStmt)
    (hNoFunc : ∀ name params rets body,
      stmt ≠ Yul.YulStmt.funcDef name params rets body) :
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative [stmt] =
      match Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative [stmt] with
      | .ok dispatcher =>
          .ok { dispatcher := .Block dispatcher
                functions :=
                  (∅ :
                    Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) }
      | .error err => .error err :=
  Compiler.Proofs.YulGeneration.Backends.Native.lowerRuntimeContractNative_single_stmt_eq_lowerStmtsNative
    stmt hNoFunc

private noncomputable def simpleStorageNativeRuntimeDispatcherStmts :
    List EvmYul.Yul.Ast.Stmt :=
  match
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
      [Compiler.CodegenCommon.initFreeMemoryPointer,
       Compiler.CodegenCommon.buildSwitch
        simpleStorageIRContract.functions none none] with
  | .ok stmts => stmts
  | .error _ => []

private noncomputable def simpleStorageNativeDispatcherStmts :
    List EvmYul.Yul.Ast.Stmt :=
  match
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
      [Compiler.CodegenCommon.buildSwitch
        simpleStorageIRContract.functions none none] with
  | .ok stmts => stmts
  | .error _ => []

/-- The executable SimpleStorage native witness is exactly the statement
lowering of the single emitted dispatcher shell.

This exposes the concrete lowered dispatcher block without unfolding the
computed native witness in later selector-case proofs. -/
private theorem simpleStorageNativeContract_dispatcher_eq_lowered_stmts :
    Compiler.SimpleStorageNativeWitness.nativeContract.dispatcher =
      .Block simpleStorageNativeRuntimeDispatcherStmts := by
  have hOuter := Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq
  obtain ⟨dispatcher, hDispatcher, hContract⟩ :=
    Compiler.Proofs.YulGeneration.Backends.Native.lowerRuntimeContractNative_emitYul_noMapping_ok_dispatcher
      simpleStorageIRContract Compiler.SimpleStorageNativeWitness.nativeContract
      (by rfl) (by rfl) (by rfl) (by rfl) hOuter
  rw [hContract]
  simp [simpleStorageNativeRuntimeDispatcherStmts, hDispatcher]

/-- A `.block` head in the native lowering surfaces as a singleton `.Block`
output when the lowering succeeds.

This is the structural lemma that lets the SimpleStorage native dispatcher
bridge be peeled past its outer block wrapper without unfolding `buildSwitch`.
-/
private theorem lowerStmtsNative_single_block_ok_singleton
    (stmts : List Yul.YulStmt)
    (lowered : List EvmYul.Yul.Ast.Stmt)
    (h : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
            [Yul.YulStmt.block stmts] = .ok lowered) :
    ∃ inner, lowered = [.Block inner] := by
  exact Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNative_single_block_ok_singleton
    stmts lowered h

/-- The `simpleStorageNativeDispatcherStmts` lowering succeeds and equals the
SimpleStorage native witness dispatcher contents.

The outer success is inherited from
`Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq` (which
itself uses the existing `native_decide` trust chain on the runtime witness),
combined with the structural single-statement equation. -/
private theorem simpleStorageNativeDispatcherStmts_lowering_ok :
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
        [Compiler.CodegenCommon.buildSwitch
          simpleStorageIRContract.functions none none] =
      .ok simpleStorageNativeDispatcherStmts := by
  obtain ⟨lowered, hLower⟩ :=
    Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNative_ok_of_yulStmtsContainFuncDef_false
      [Compiler.CodegenCommon.buildSwitch
        simpleStorageIRContract.functions none none] (by
          have hBodies :
              ∀ fn, fn ∈ simpleStorageIRContract.functions →
                Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
                  fn.body = false := by
            intro fn hmem
            simp [simpleStorageIRContract] at hmem ⊢
            rcases hmem with rfl | rfl <;> rfl
          have hSwitch :=
            Compiler.Proofs.YulGeneration.Backends.Native.buildSwitch_noFuncDefs_noFallback_noReceive
              simpleStorageIRContract.functions hBodies
          simpa [Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef,
            hSwitch])
  simp [simpleStorageNativeDispatcherStmts, hLower]

/-- The SimpleStorage native dispatcher statement list is a singleton `.Block`.

Reason: `buildSwitch` produces a `Yul.YulStmt.block`, which the native lowering
maps to `[.Block inner]` for the lowered inner statements. Combined with the
fact that the lowering succeeds (above), this exposes the inner block shape
without further computation. -/
private theorem simpleStorageNativeRuntimeDispatcherStmts_exists_init_block :
    ∃ (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat),
      simpleStorageNativeRuntimeDispatcherStmts =
        [.ExprStmtCall
          (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
            (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
               Yul.YulExpr.lit 128])),
         .Block inner] ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
          [Compiler.CodegenCommon.initFreeMemoryPointer,
           Compiler.CodegenCommon.buildSwitch simpleStorageIRContract.functions none none])
        0
        simpleStorageBuildSwitchBody =
        .ok (inner, next) := by
  have hOuter := Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq
  obtain ⟨dispatcher, hDispatcher, _hContract⟩ :=
    Compiler.Proofs.YulGeneration.Backends.Native.lowerRuntimeContractNative_emitYul_noMapping_ok_dispatcher
      simpleStorageIRContract Compiler.SimpleStorageNativeWitness.nativeContract
      (by rfl) (by rfl) (by rfl) (by rfl) hOuter
  unfold simpleStorageNativeRuntimeDispatcherStmts
  rw [hDispatcher]
  unfold Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative at hDispatcher
  dsimp at hDispatcher
  cases hLowerList :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
          [Compiler.CodegenCommon.initFreeMemoryPointer,
           Compiler.CodegenCommon.buildSwitch simpleStorageIRContract.functions none none])
        0
        [Compiler.CodegenCommon.initFreeMemoryPointer,
         Compiler.CodegenCommon.buildSwitch simpleStorageIRContract.functions none none] with
  | error err =>
      rw [hLowerList] at hDispatcher
      simp at hDispatcher
  | ok pair =>
      rcases pair with ⟨lowered, finalNext⟩
      rw [hLowerList] at hDispatcher
      simp at hDispatcher
      subst dispatcher
      rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons] at hLowerList
      simp [Compiler.CodegenCommon.initFreeMemoryPointer, Bind.bind,
        Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_expr,
        Except.bind, Pure.pure, Except.pure] at hLowerList
      rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons] at hLowerList
      simp [Compiler.CodegenCommon.buildSwitch,
        Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_block,
        simpleStorageBuildSwitchBody, simpleStorageBuildSwitchSourceCases,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at hLowerList
      cases hInner :
          Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
            (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
              [Compiler.CodegenCommon.initFreeMemoryPointer,
               Compiler.CodegenCommon.buildSwitch simpleStorageIRContract.functions none none])
            0
            simpleStorageBuildSwitchBody with
      | error err =>
          have hInner' :
              Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
                (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
                  [Yul.YulStmt.exprStmt
                    (Yul.YulExpr.call "mstore"
                      [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                       Yul.YulExpr.lit 128]),
                   Yul.YulStmt.block
                    [Yul.YulStmt.let_ "__has_selector"
                      (Yul.YulExpr.call "iszero"
                        [Yul.YulExpr.call "lt"
                          [Yul.YulExpr.call "calldatasize" [],
                           Yul.YulExpr.lit 4]]),
                     Yul.YulStmt.if_
                      (Yul.YulExpr.call "iszero"
                        [Yul.YulExpr.ident "__has_selector"])
                      (Compiler.CodegenCommon.defaultDispatchCase none none),
                     Yul.YulStmt.if_ (Yul.YulExpr.ident "__has_selector")
                      [Yul.YulStmt.switch
                        (Yul.YulExpr.call "shr"
                          [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                           Yul.YulExpr.call "calldataload"
                            [Yul.YulExpr.lit 0]])
                        simpleStorageBuildSwitchSourceCases
                        (some (Compiler.CodegenCommon.defaultDispatchCase
                          none none))]]])
                0
                [Yul.YulStmt.let_ "__has_selector"
                  (Yul.YulExpr.call "iszero"
                    [Yul.YulExpr.call "lt"
                      [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]),
                 Yul.YulStmt.if_
                  (Yul.YulExpr.call "iszero"
                    [Yul.YulExpr.ident "__has_selector"])
                  (Compiler.CodegenCommon.defaultDispatchCase none none),
                 Yul.YulStmt.if_ (Yul.YulExpr.ident "__has_selector")
                  [Yul.YulStmt.switch
                    (Yul.YulExpr.call "shr"
                      [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                       Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
                    simpleStorageBuildSwitchSourceCases
                    (some (Compiler.CodegenCommon.defaultDispatchCase
                      none none))]] =
                .error err := by
            simpa [Compiler.CodegenCommon.initFreeMemoryPointer,
              Compiler.CodegenCommon.buildSwitch, simpleStorageBuildSwitchBody,
              simpleStorageBuildSwitchSourceCases] using hInner
          have hBad : (Except.error err : Except NativeLoweringError
              (List EvmYul.Yul.Ast.Stmt × Nat)) = .ok (lowered, finalNext) := by
            have hInnerMap :
                Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
                  (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
                    [Yul.YulStmt.exprStmt
                      (Yul.YulExpr.call "mstore"
                        [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                         Yul.YulExpr.lit 128]),
                     Yul.YulStmt.block
                      [Yul.YulStmt.let_ "__has_selector"
                        (Yul.YulExpr.call "iszero"
                          [Yul.YulExpr.call "lt"
                            [Yul.YulExpr.call "calldatasize" [],
                             Yul.YulExpr.lit 4]]),
                       Yul.YulStmt.if_
                        (Yul.YulExpr.call "iszero"
                          [Yul.YulExpr.ident "__has_selector"])
                        (Compiler.CodegenCommon.defaultDispatchCase none none),
                       Yul.YulStmt.if_ (Yul.YulExpr.ident "__has_selector")
                        [Yul.YulStmt.switch
                          (Yul.YulExpr.call "shr"
                            [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                             Yul.YulExpr.call "calldataload"
                              [Yul.YulExpr.lit 0]])
                          (List.map
                            (fun fn =>
                              (fn.selector,
                                Compiler.CodegenCommon.dispatchBody fn.payable
                                  (toString fn.name ++ toString "()")
                                  (Compiler.CodegenCommon.calldatasizeGuard
                                    fn.params.length :: fn.body)))
                            simpleStorageIRContract.functions)
                          (some (Compiler.CodegenCommon.defaultDispatchCase
                            none none))]]])
                  0
                  [Yul.YulStmt.let_ "__has_selector"
                    (Yul.YulExpr.call "iszero"
                      [Yul.YulExpr.call "lt"
                        [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]),
                   Yul.YulStmt.if_
                    (Yul.YulExpr.call "iszero"
                      [Yul.YulExpr.ident "__has_selector"])
                    (Compiler.CodegenCommon.defaultDispatchCase none none),
                   Yul.YulStmt.if_ (Yul.YulExpr.ident "__has_selector")
                    [Yul.YulStmt.switch
                      (Yul.YulExpr.call "shr"
                        [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                         Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
                      (List.map
                        (fun fn =>
                          (fn.selector,
                            Compiler.CodegenCommon.dispatchBody fn.payable
                              (toString fn.name ++ toString "()")
                              (Compiler.CodegenCommon.calldatasizeGuard
                                fn.params.length :: fn.body)))
                        simpleStorageIRContract.functions)
                      (some (Compiler.CodegenCommon.defaultDispatchCase
                        none none))]] =
                  .error err := by
              simpa [simpleStorageBuildSwitchSourceCases] using hInner'
            simp [hInnerMap, simpleStorageBuildSwitchSourceCases] at hLowerList
          cases hBad
      | ok innerPair =>
          rcases innerPair with ⟨inner, innerNext⟩
          have hInner' :
              Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
                (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
                  [Yul.YulStmt.exprStmt
                    (Yul.YulExpr.call "mstore"
                      [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                       Yul.YulExpr.lit 128]),
                   Yul.YulStmt.block
                    [Yul.YulStmt.let_ "__has_selector"
                      (Yul.YulExpr.call "iszero"
                        [Yul.YulExpr.call "lt"
                          [Yul.YulExpr.call "calldatasize" [],
                           Yul.YulExpr.lit 4]]),
                     Yul.YulStmt.if_
                      (Yul.YulExpr.call "iszero"
                        [Yul.YulExpr.ident "__has_selector"])
                      (Compiler.CodegenCommon.defaultDispatchCase none none),
                     Yul.YulStmt.if_ (Yul.YulExpr.ident "__has_selector")
                      [Yul.YulStmt.switch
                        (Yul.YulExpr.call "shr"
                          [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                           Yul.YulExpr.call "calldataload"
                            [Yul.YulExpr.lit 0]])
                        simpleStorageBuildSwitchSourceCases
                        (some (Compiler.CodegenCommon.defaultDispatchCase
                          none none))]]])
                0
                [Yul.YulStmt.let_ "__has_selector"
                  (Yul.YulExpr.call "iszero"
                    [Yul.YulExpr.call "lt"
                      [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]),
                 Yul.YulStmt.if_
                  (Yul.YulExpr.call "iszero"
                    [Yul.YulExpr.ident "__has_selector"])
                  (Compiler.CodegenCommon.defaultDispatchCase none none),
                 Yul.YulStmt.if_ (Yul.YulExpr.ident "__has_selector")
                  [Yul.YulStmt.switch
                    (Yul.YulExpr.call "shr"
                      [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                       Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
                    simpleStorageBuildSwitchSourceCases
                    (some (Compiler.CodegenCommon.defaultDispatchCase
                      none none))]] =
                .ok (inner, innerNext) := by
            simpa [Compiler.CodegenCommon.initFreeMemoryPointer,
              Compiler.CodegenCommon.buildSwitch, simpleStorageBuildSwitchBody,
              simpleStorageBuildSwitchSourceCases] using hInner
          have hLowerList' :
              (Except.ok
                ([EvmYul.Yul.Ast.Stmt.ExprStmtCall
                    (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
                      (Yul.YulExpr.call "mstore"
                        [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                         Yul.YulExpr.lit 128])),
                  EvmYul.Yul.Ast.Stmt.Block inner],
                 innerNext) :
                Except NativeLoweringError (List EvmYul.Yul.Ast.Stmt × Nat)) =
                (Except.ok (lowered, finalNext) :
                  Except NativeLoweringError (List EvmYul.Yul.Ast.Stmt × Nat)) := by
            have hInnerMap :
                Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
                  (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
                    [Yul.YulStmt.exprStmt
                      (Yul.YulExpr.call "mstore"
                        [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                         Yul.YulExpr.lit 128]),
                     Yul.YulStmt.block
                      [Yul.YulStmt.let_ "__has_selector"
                        (Yul.YulExpr.call "iszero"
                          [Yul.YulExpr.call "lt"
                            [Yul.YulExpr.call "calldatasize" [],
                             Yul.YulExpr.lit 4]]),
                       Yul.YulStmt.if_
                        (Yul.YulExpr.call "iszero"
                          [Yul.YulExpr.ident "__has_selector"])
                        (Compiler.CodegenCommon.defaultDispatchCase none none),
                       Yul.YulStmt.if_ (Yul.YulExpr.ident "__has_selector")
                        [Yul.YulStmt.switch
                          (Yul.YulExpr.call "shr"
                            [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                             Yul.YulExpr.call "calldataload"
                              [Yul.YulExpr.lit 0]])
                          (List.map
                            (fun fn =>
                              (fn.selector,
                                Compiler.CodegenCommon.dispatchBody fn.payable
                                  (toString fn.name ++ toString "()")
                                  (Compiler.CodegenCommon.calldatasizeGuard
                                    fn.params.length :: fn.body)))
                            simpleStorageIRContract.functions)
                          (some (Compiler.CodegenCommon.defaultDispatchCase
                            none none))]]])
                  0
                  [Yul.YulStmt.let_ "__has_selector"
                    (Yul.YulExpr.call "iszero"
                      [Yul.YulExpr.call "lt"
                        [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]),
                   Yul.YulStmt.if_
                    (Yul.YulExpr.call "iszero"
                      [Yul.YulExpr.ident "__has_selector"])
                    (Compiler.CodegenCommon.defaultDispatchCase none none),
                   Yul.YulStmt.if_ (Yul.YulExpr.ident "__has_selector")
                    [Yul.YulStmt.switch
                      (Yul.YulExpr.call "shr"
                        [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                         Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
                      (List.map
                        (fun fn =>
                          (fn.selector,
                            Compiler.CodegenCommon.dispatchBody fn.payable
                              (toString fn.name ++ toString "()")
                              (Compiler.CodegenCommon.calldatasizeGuard
                                fn.params.length :: fn.body)))
                        simpleStorageIRContract.functions)
                      (some (Compiler.CodegenCommon.defaultDispatchCase
                        none none))]] =
                  .ok (inner, innerNext) := by
              simpa [simpleStorageBuildSwitchSourceCases] using hInner'
            simpa [hInnerMap, simpleStorageBuildSwitchSourceCases] using hLowerList
          simp at hLowerList'
          rcases hLowerList' with ⟨hLowered, hNext⟩
          subst lowered
          subst finalNext
          exact ⟨inner, innerNext, by simp, by
            simpa [simpleStorageBuildSwitchBody, simpleStorageBuildSwitchSourceCases]
              using hInner⟩

private noncomputable def simpleStorageNativeDispatcherInnerStmts :
    List EvmYul.Yul.Ast.Stmt :=
  Classical.choose simpleStorageNativeRuntimeDispatcherStmts_exists_init_block

private noncomputable def simpleStorageNativeDispatcherInnerNext : Nat :=
  Classical.choose
    (Classical.choose_spec simpleStorageNativeRuntimeDispatcherStmts_exists_init_block)

private theorem simpleStorageNativeRuntimeDispatcherStmts_eq_init_block :
    simpleStorageNativeRuntimeDispatcherStmts =
      [.ExprStmtCall
        (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
          (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
             Yul.YulExpr.lit 128])),
       .Block simpleStorageNativeDispatcherInnerStmts] :=
  (Classical.choose_spec
    (Classical.choose_spec
      simpleStorageNativeRuntimeDispatcherStmts_exists_init_block)).1

private theorem simpleStorageNativeDispatcherInnerStmts_lowering_ok :
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
      (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
        [Compiler.CodegenCommon.initFreeMemoryPointer,
         Compiler.CodegenCommon.buildSwitch simpleStorageIRContract.functions none none])
      0
      simpleStorageBuildSwitchBody =
      .ok (simpleStorageNativeDispatcherInnerStmts,
        simpleStorageNativeDispatcherInnerNext) :=
  (Classical.choose_spec
    (Classical.choose_spec
      simpleStorageNativeRuntimeDispatcherStmts_exists_init_block)).2

/-- Transitive form of the SimpleStorage native dispatcher shape: combining
the lowered-stmts and singleton-block equalities exposes the dispatcher value
as `.Block [.Block <inner>]`, which is the exact shape consumed by the harness
dispatcher-exec peel lemma. -/
private theorem simpleStorageNativeContract_dispatcher_eq_singleton_block_inner :
    Compiler.SimpleStorageNativeWitness.nativeContract.dispatcher =
      .Block
        [.ExprStmtCall
          (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
            (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
               Yul.YulExpr.lit 128])),
         .Block simpleStorageNativeDispatcherInnerStmts] := by
  rw [simpleStorageNativeContract_dispatcher_eq_lowered_stmts]
  congr
  exact simpleStorageNativeRuntimeDispatcherStmts_eq_init_block

/-- Reify the SimpleStorage native witness contract as a record whose
dispatcher is the doubly-blocked inner statement list.

This packages record-η with the lowered + singleton-block dispatcher
equalities so that the harness peel lemmas (which expect a
`{ dispatcher := .Block body, functions := … }` shape) apply in one rewrite. -/
private theorem simpleStorageNativeContract_eq_record_inner_block :
    Compiler.SimpleStorageNativeWitness.nativeContract =
      { dispatcher := .Block
          [.ExprStmtCall
            (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
              (Yul.YulExpr.call "mstore"
                [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                 Yul.YulExpr.lit 128])),
           .Block simpleStorageNativeDispatcherInnerStmts]
        functions :=
          Compiler.SimpleStorageNativeWitness.nativeContract.functions } := by
  have hEta : Compiler.SimpleStorageNativeWitness.nativeContract =
      (⟨Compiler.SimpleStorageNativeWitness.nativeContract.dispatcher,
        Compiler.SimpleStorageNativeWitness.nativeContract.functions⟩ :
          EvmYul.Yul.Ast.YulContract) := rfl
  rw [hEta, simpleStorageNativeContract_dispatcher_eq_singleton_block_inner]

/-- Dispatcher-exec for the SimpleStorage native witness peels TWO outer
`.Block` wrappers (the function-body wrapper installed by the dispatcher exec
plus the singleton-block emitted by `buildSwitch`'s native lowering) into a
direct `EvmYul.Yul.exec` over the inner statement list.

This collapses the bridge's dispatcher invocation into the same shape the
harness's per-selector body lemmas already speak about, in preparation for
discharging the bridge from those lemmas. -/
private theorem simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec
    (peeledFuel : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (Nat.succ (Nat.succ (peeledFuel + 6)))
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) =
      EvmYul.Yul.exec (peeledFuel + 5)
        (.Block simpleStorageNativeDispatcherInnerStmts)
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots ∅) := by
  rw [simpleStorageNativeContract_eq_record_inner_block]
  rw [Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult_block_dispatcher_eq_exec_block
    (peeledFuel + 6)
    [.ExprStmtCall
      (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.call "mstore"
          [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
           Yul.YulExpr.lit 128])),
     .Block simpleStorageNativeDispatcherInnerStmts]
    Compiler.SimpleStorageNativeWitness.nativeContract.functions
    tx storage observableSlots]
  rw [Compiler.Proofs.YulGeneration.Backends.Native.exec_block_cons_initFreeMemoryPointer_eq
    peeledFuel [.Block simpleStorageNativeDispatcherInnerStmts]
    { dispatcher := EvmYul.Yul.Ast.Stmt.Block
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
            (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
               Yul.YulExpr.lit 128])),
         EvmYul.Yul.Ast.Stmt.Block simpleStorageNativeDispatcherInnerStmts],
      functions := Compiler.SimpleStorageNativeWitness.nativeContract.functions }
    tx storage observableSlots]
  rw [show peeledFuel + 6 =
      Nat.succ (Nat.succ (peeledFuel + 4)) by omega]
  rw [Compiler.Proofs.YulGeneration.Backends.Native.exec_singleton_block_eq_exec_block]

/-- A successful lowering of a singleton `[.block stmts]` reveals exactly the
inner statement-list lowering. This is the structural counterpart of
`lowerStmtsNative_single_block_ok_singleton`: instead of merely existing, the
`inner` argument is the *output* of the inner statement-list lowering. -/
private theorem lowerStmtsNative_block_stmts_eq
    (stmts : List Yul.YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (h : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
            [Yul.YulStmt.block stmts] = .ok [.Block inner]) :
    ∃ next : Nat,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
          [Yul.YulStmt.block stmts])
        0 stmts = .ok (inner, next) := by
  exact Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNative_block_stmts_eq
    stmts inner h

/-- A `.let_`-headed statement-list lowering peels its head into a singleton
`.Let` statement and threads the unchanged switch counter through the tail.
This generic peel is the per-statement complement of
`lowerStmtsNative_block_stmts_eq`: combined, they reduce a successful native
lowering of a `.let_`-headed block to the lowering of its tail. -/
private theorem lowerStmtsNativeWithSwitchIds_let_head_eq
    (reservedNames : List String) (n0 : Nat)
    (name : String) (value : Yul.YulExpr)
    (rest : List Yul.YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
            reservedNames n0
            (Yul.YulStmt.let_ name value :: rest) = .ok (inner, next)) :
    ∃ rest' : List EvmYul.Yul.Ast.Stmt,
      inner = EvmYul.Yul.Ast.Stmt.Let [name]
                (some
                  (Compiler.Proofs.YulGeneration.Backends.lowerExprNative value))
                :: rest' ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames n0 rest = .ok (rest', next) := by
  exact Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_let_head_eq
      reservedNames n0 name value
      rest inner next h

/-- An `.if_`-headed statement-list lowering peels its head into a singleton
`.If` statement and threads the body's switch-counter advance through to the
tail. This is the per-statement complement of
`lowerStmtsNativeWithSwitchIds_let_head_eq` for the `if_` case: combined with
`lowerStmtsNative_block_stmts_eq`, it lets a successful native lowering of a
block be peeled past an `.if_`-headed source statement. -/
private theorem lowerStmtsNativeWithSwitchIds_if_head_eq
    (reservedNames : List String) (n0 : Nat)
    (cond : Yul.YulExpr) (body : List Yul.YulStmt)
    (rest : List Yul.YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
            reservedNames n0
            (Yul.YulStmt.if_ cond body :: rest) = .ok (inner, next)) :
    ∃ (body' : List EvmYul.Yul.Ast.Stmt) (midN : Nat)
      (rest' : List EvmYul.Yul.Ast.Stmt),
      inner = EvmYul.Yul.Ast.Stmt.If
                (Compiler.Proofs.YulGeneration.Backends.lowerExprNative cond)
                body' :: rest' ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames n0 body = .ok (body', midN) ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames midN rest = .ok (rest', next) := by
  exact Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_if_head_eq
      reservedNames n0 cond body rest
      inner next h

set_option linter.unusedSimpArgs false in
/-- A singleton `.switch`-headed statement-list lowering reduces to a singleton
`.lowerNativeSwitchBlock` over the same source expression. This is the
companion of `lowerStmtsNativeWithSwitchIds_let_head_eq` and `_if_head_eq`
specialized to a single source-level `switch` statement (no tail), which is
exactly the shape produced by the body of `buildSwitch`'s selector-hit `if`.
The case-bodies and default-body lowerings remain abstract because their
shape depends on the concrete contract `funcs` list. -/
private theorem lowerStmtsNativeWithSwitchIds_singleton_switch_eq
    (reservedNames : List String) (n0 : Nat)
    (expr : Yul.YulExpr) (cases : List (Nat × List Yul.YulStmt))
    (defaultCase : Option (List Yul.YulStmt))
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [Yul.YulStmt.switch expr cases defaultCase] = .ok (inner, next)) :
    ∃ (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      inner = [Backends.lowerNativeSwitchBlock expr
        (Backends.freshNativeSwitchId reservedNames n0) cases' default'] := by
  exact Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_singleton_switch_eq
      reservedNames n0 expr
      cases defaultCase inner next h

/-- The head of the SimpleStorage native dispatcher inner-block is the lowered
`let __has_selector := ...` statement. This peels one further layer beyond the
singleton-block extraction (`simpleStorageNativeDispatcherStmts_eq_singleton_block`)
by applying the cons/`_let` lowering equations to the head of `buildSwitch`'s
3-statement block. The remaining tail is left abstract — downstream peels will
expose the second and third statements. -/
private theorem simpleStorageNativeDispatcherInnerStmts_head_let_exists :
    ∃ (e : EvmYul.Yul.Ast.Expr) (rest : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        EvmYul.Yul.Ast.Stmt.Let ["__has_selector"] (some e) :: rest := by
  have hInner := simpleStorageNativeDispatcherInnerStmts_lowering_ok
  -- `buildSwitch ssIRC.functions none none` unfolds (definitionally) to a
  -- 3-statement `YulStmt.block` whose head is `let __has_selector := …`, so
  -- `hInner` is already a `let_`-headed lowering at the source spine.
  obtain ⟨rest', hSplit, _⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  exact ⟨_, rest', hSplit⟩

/-- The first two statements of the SimpleStorage native dispatcher inner-block
are exactly the lowered `let __has_selector := ...` and the lowered selector-miss
guard `if iszero(__has_selector) { revert(0,0) }`. This peels the second
statement of `buildSwitch`'s 3-statement source block by chaining
`lowerStmtsNative_block_stmts_eq`, `lowerStmtsNativeWithSwitchIds_let_head_eq`,
and `lowerStmtsNativeWithSwitchIds_if_head_eq`. -/
private theorem simpleStorageNativeDispatcherInnerStmts_let_if_head_exists :
    ∃ (e : EvmYul.Yul.Ast.Expr) (c : EvmYul.Yul.Ast.Expr)
      (body : List EvmYul.Yul.Ast.Stmt) (rest : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        EvmYul.Yul.Ast.Stmt.Let ["__has_selector"] (some e) ::
          EvmYul.Yul.Ast.Stmt.If c body ::
          rest := by
  have hInner := simpleStorageNativeDispatcherInnerStmts_lowering_ok
  obtain ⟨rest', hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body', _midN, rest'', hIf, _, _⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  rw [hIf] at hLet
  exact ⟨_, _, body', rest'', hLet⟩

/-- The full inner-block of the SimpleStorage native dispatcher has exactly the
expected three-statement shape: the lowered `let __has_selector := …`, the
selector-miss `if iszero(__has_selector) { … }` guard, and the selector-hit
`if __has_selector { switch … }` body. The trailing list is empty because
`buildSwitch` produces a 3-statement source block. -/
private theorem simpleStorageNativeDispatcherInnerStmts_eq_let_if_if :
    ∃ (e : EvmYul.Yul.Ast.Expr) (c1 : EvmYul.Yul.Ast.Expr)
      (body1 : List EvmYul.Yul.Ast.Stmt)
      (c2 : EvmYul.Yul.Ast.Expr) (body2 : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"] (some e),
         EvmYul.Yul.Ast.Stmt.If c1 body1,
         EvmYul.Yul.Ast.Stmt.If c2 body2] := by
  have hInner := simpleStorageNativeDispatcherInnerStmts_lowering_ok
  obtain ⟨rest', hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, rest'', hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨body2', _, rest''', hIf2, _, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  rw [hIf2] at hIf1
  rw [hIf1] at hLet
  exact ⟨_, _, body1', _, body2', hLet⟩

/-- The lowered RHS expression of the SimpleStorage native dispatcher's
`__has_selector` let. Pinned via `Classical.choose` from the let/if/if shape
existential so it can be referenced by downstream proofs without re-`obtain`-ing
the witness each time. -/
private noncomputable def simpleStorageNativeDispatcher_letValue :
    EvmYul.Yul.Ast.Expr :=
  Classical.choose simpleStorageNativeDispatcherInnerStmts_eq_let_if_if

/-- The lowered condition of the SimpleStorage native dispatcher's
selector-miss `if iszero(__has_selector) { … }` guard. -/
private noncomputable def simpleStorageNativeDispatcher_if1Cond :
    EvmYul.Yul.Ast.Expr :=
  Classical.choose
    (Classical.choose_spec simpleStorageNativeDispatcherInnerStmts_eq_let_if_if)

/-- The lowered body of the SimpleStorage native dispatcher's selector-miss
guard (the `revert(0,0)` revert path). -/
private noncomputable def simpleStorageNativeDispatcher_if1Body :
    List EvmYul.Yul.Ast.Stmt :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec simpleStorageNativeDispatcherInnerStmts_eq_let_if_if))

/-- The lowered condition of the SimpleStorage native dispatcher's
selector-hit `if __has_selector { switch … }` body. -/
private noncomputable def simpleStorageNativeDispatcher_if2Cond :
    EvmYul.Yul.Ast.Expr :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          simpleStorageNativeDispatcherInnerStmts_eq_let_if_if)))

/-- The lowered body of the SimpleStorage native dispatcher's selector-hit
`if __has_selector { switch … }` body — i.e., the singleton list containing
the lowered `switch` over the three generated cases. -/
private noncomputable def simpleStorageNativeDispatcher_if2Body :
    List EvmYul.Yul.Ast.Stmt :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            simpleStorageNativeDispatcherInnerStmts_eq_let_if_if))))

/-- Closed-form decomposition of the SimpleStorage native dispatcher inner
statement list using the named witness defs. Eliminates the existential
boilerplate from the `_eq_let_if_if` lemma so future selector-case proofs can
rewrite the dispatcher inner-stmts to a literal 3-element list. -/
private theorem simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if :
    simpleStorageNativeDispatcherInnerStmts =
      [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
          (some simpleStorageNativeDispatcher_letValue),
       EvmYul.Yul.Ast.Stmt.If
          simpleStorageNativeDispatcher_if1Cond
          simpleStorageNativeDispatcher_if1Body,
       EvmYul.Yul.Ast.Stmt.If
          simpleStorageNativeDispatcher_if2Cond
          simpleStorageNativeDispatcher_if2Body] :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            simpleStorageNativeDispatcherInnerStmts_eq_let_if_if))))

/-- Composed structural form of the SimpleStorage native dispatcher exec:
the doubly-blocked dispatcher is exposed at the concrete inner three-statement
spine using the pinned named witnesses. This combines
`simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec` with
`simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if`, replacing the
existential let/if/if shape with a concrete equation in named witnesses. -/
private theorem simpleStorageNativeContract_dispatcherExec_eq_named_let_if_if_block_exec
    (peeledFuel : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (Nat.succ (Nat.succ (peeledFuel + 6)))
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) =
      EvmYul.Yul.exec (peeledFuel + 5)
        (.Block
          [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
              (some simpleStorageNativeDispatcher_letValue),
           EvmYul.Yul.Ast.Stmt.If
              simpleStorageNativeDispatcher_if1Cond
              simpleStorageNativeDispatcher_if1Body,
           EvmYul.Yul.Ast.Stmt.If
              simpleStorageNativeDispatcher_if2Cond
              simpleStorageNativeDispatcher_if2Body])
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots ∅) := by
  rw [simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec,
      simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if]

/-- Concrete head exposure of the SimpleStorage native dispatcher inner-block:
its first statement is the lowered `let __has_selector := iszero(lt(calldatasize(), 4))`
that `buildSwitch` emits, with the source-Yul RHS pinned explicitly. This is
the same peel as `simpleStorageNativeDispatcherInnerStmts_head_let_exists` but
exposes the *concrete* lowered RHS (not just an abstract Lean witness), so the
`Classical.choose`-pinned `simpleStorageNativeDispatcher_letValue` can be
equated to it via head injection. -/
private theorem simpleStorageNativeDispatcherInnerStmts_concrete_let_head :
    ∃ rest : List EvmYul.Yul.Ast.Stmt,
      simpleStorageNativeDispatcherInnerStmts =
        EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some
              (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
                (Yul.YulExpr.call "iszero"
                  [Yul.YulExpr.call "lt"
                    [Yul.YulExpr.call "calldatasize" [],
                     Yul.YulExpr.lit 4]]))) :: rest := by
  have hInner := simpleStorageNativeDispatcherInnerStmts_lowering_ok
  obtain ⟨rest', hSplit, _⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  exact ⟨rest', hSplit⟩

/-- Concrete-form equation for the SimpleStorage native dispatcher's full inner
3-statement block, pinning *all three* source-Yul expressions (the let RHS, the
selector-miss `iszero(__has_selector)` guard, and the selector-hit
`__has_selector` guard) to the literal Yul expressions emitted by
`buildSwitch`. Only the two `If` bodies remain existential, since they depend
on the lowering of the inner switch over the generated cases. This is the
companion of `simpleStorageNativeDispatcherInnerStmts_eq_let_if_if` with
abstract Yul witnesses replaced by concrete syntax. -/
private theorem simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_if :
    ∃ (body1 body2 : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some
              (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
                (Yul.YulExpr.call "iszero"
                  [Yul.YulExpr.call "lt"
                    [Yul.YulExpr.call "calldatasize" [],
                     Yul.YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
              (Yul.YulExpr.call "iszero"
                [Yul.YulExpr.ident "__has_selector"]))
            body1,
         EvmYul.Yul.Ast.Stmt.If
            (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
              (Yul.YulExpr.ident "__has_selector"))
            body2] := by
  have hInner := simpleStorageNativeDispatcherInnerStmts_lowering_ok
  obtain ⟨rest', hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, rest'', hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨body2', _, rest''', hIf2, _, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  rw [hIf2] at hIf1
  rw [hIf1] at hLet
  exact ⟨body1', body2', hLet⟩

/-- Strengthened concrete-form equation for the SimpleStorage native dispatcher
inner-block: same as `simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_if`
except the body of the second (selector-hit) `If` is pinned to a singleton
`lowerNativeSwitchBlock` over the source-Yul `selectorExpr` scrutinee. The
selector cases and default body remain existential because they depend on the
contract's `functions` list. This is the next dispatcher peel beyond the
let/if/if shape and is the foundation for replacing the Classical.choose-pinned
`simpleStorageNativeDispatcher_if2Body` with a concrete switch block. -/
private theorem simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero"
                [Yul.YulExpr.call "lt"
                  [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident "__has_selector"]))
            body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases' default']] := by
  have hInner := simpleStorageNativeDispatcherInnerStmts_lowering_ok
  obtain ⟨_, hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, _, hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨_, _, _, hIf2, hBody2, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  obtain ⟨cases', default', hBody2Eq⟩ :=
    lowerStmtsNativeWithSwitchIds_singleton_switch_eq _ _ _ _ _ _ _ hBody2
  rw [hBody2Eq] at hIf2; rw [hIf2] at hIf1; rw [hIf1] at hLet
  exact ⟨body1', _, cases', default', hLet⟩

/-- WithSwitchIds-form companion of `lowerStmtsNative_revert_zero_zero`: at any
`reservedNames`/`nextSwitchId` pair, the singleton list `[expr (revert(0,0))]`
emitted by `defaultDispatchCase none none` lowers to
`[nativeRevertZeroZeroStmt]` while leaving the switch counter unchanged. The
dispatcher peel uses `lowerStmtsNativeWithSwitchIds` directly (via
`_block_stmts_eq` / `_let_head_eq` / `_if_head_eq`), so the wrapper-level
`lowerStmtsNative_revert_zero_zero` lemma alone is insufficient when pinning
the selector-miss `If` body. -/
private theorem lowerStmtsNativeWithSwitchIds_revert_zero_zero
    (reservedNames : List String) (n : Nat) :
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames n
        [Yul.YulStmt.exprStmt (Yul.YulExpr.call "revert"
          [Yul.YulExpr.lit 0, Yul.YulExpr.lit 0])] =
      .ok ([Backends.Native.nativeRevertZeroZeroStmt], n) := by
  exact Backends.Native.lowerStmtsNativeWithSwitchIds_revert_zero_zero
    reservedNames n

set_option linter.unusedSimpArgs false in
/-- Strengthened companion of `lowerStmtsNativeWithSwitchIds_singleton_switch_eq`:
when the source-level switch's `defaultCase` is fixed to the
`defaultDispatchCase none none` body — namely the singleton list
`[expr (revert(0,0))]` — the lowered default body is concretely
`[nativeRevertZeroZeroStmt]`. The lowered case bodies remain existential
(they depend on the contract `funcs` list). This pins the previously-existential
`default'` produced by `_singleton_switch_eq`, unblocking downstream proofs
that need to plug the lowered-switch exec into a concrete default-revert
endpoint. -/
private theorem lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq
    (reservedNames : List String) (n0 : Nat)
    (expr : Yul.YulExpr) (cases : List (Nat × List Yul.YulStmt))
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [Yul.YulStmt.switch expr cases
              (some [Yul.YulStmt.exprStmt (Yul.YulExpr.call "revert"
                [Yul.YulExpr.lit 0, Yul.YulExpr.lit 0])])] = .ok (inner, next)) :
    ∃ (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      inner = [Backends.lowerNativeSwitchBlock expr
        (Backends.freshNativeSwitchId reservedNames n0) cases'
        [Backends.Native.nativeRevertZeroZeroStmt]] := by
  exact Backends.Native.lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq
    reservedNames n0 expr cases inner next h

set_option linter.unusedSimpArgs false in
/-- Source-lowered companion of `_singleton_switch_revert_default_eq`: also
exposes the `lowerSwitchCasesNativeWithSwitchIds` equation linking the source
case list to the lowered `cases'`. Downstream selector-miss reductions chain
this with `lowerSwitchCasesNativeWithSwitchIds_tags_eq` /
`lowerSwitchCasesNativeWithSwitchIds_find?_none` to lift source-level selector
facts through the lowering. -/
private theorem lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered
    (reservedNames : List String) (n0 : Nat)
    (expr : Yul.YulExpr) (cases : List (Nat × List Yul.YulStmt))
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [Yul.YulStmt.switch expr cases
              (some [Yul.YulStmt.exprStmt (Yul.YulExpr.call "revert"
                [Yul.YulExpr.lit 0, Yul.YulExpr.lit 0])])] = .ok (inner, next)) :
    ∃ (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      inner = [Backends.lowerNativeSwitchBlock expr
        (Backends.freshNativeSwitchId reservedNames n0) cases'
        [Backends.Native.nativeRevertZeroZeroStmt]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) cases =
          .ok (cases', midN) := by
  exact Backends.Native.lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered
    reservedNames n0 expr cases inner next h

/-- Source-lowered companion of `_eq_concrete_let_if_switchSingleton_revert_default`:
additionally exposes the lowering equation for the buildSwitch-emitted source
case list `simpleStorageBuildSwitchSourceCases` into the lowered `cases'`.
Bridge lemma for the selector-miss closed-form: chained with
`lowerSwitchCasesNativeWithSwitchIds_tags_eq` it converts source-level
selector facts into lowered-level `find?` results. -/
private theorem simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default_sourceLowered :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident "__has_selector"])) body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [Backends.Native.nativeRevertZeroZeroStmt]]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  have hInner := simpleStorageNativeDispatcherInnerStmts_lowering_ok
  obtain ⟨rest', hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1, body1Next, rest'', hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨body2, _body2Next, rest''', hIf2, hBody2, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  obtain ⟨cases', midN, hSwitch, hLowerCases⟩ :=
    lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered
      _ _ _ _ _ _ hBody2
  rw [hSwitch] at hIf2
  rw [hIf2] at hIf1
  rw [hIf1] at hLet
  let reservedNames : List String :=
    Backends.yulStmtsIdentifierNames
      [Compiler.CodegenCommon.initFreeMemoryPointer,
       Compiler.CodegenCommon.buildSwitch simpleStorageIRContract.functions none none]
  refine ⟨body1, reservedNames, body1Next, cases', midN, ?_, ?_⟩
  · simpa [reservedNames] using hLet
  · simpa [reservedNames, simpleStorageBuildSwitchSourceCases] using hLowerCases

private theorem simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero"
                [Yul.YulExpr.call "lt"
                  [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident "__has_selector"]))
            body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases'
              [Backends.Native.nativeRevertZeroZeroStmt]]] := by
  obtain ⟨body1, reservedNames, n0, cases', _, hInner, _⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default_sourceLowered
  exact ⟨body1, Backends.freshNativeSwitchId reservedNames n0, cases', hInner⟩

/-- The `Classical.choose`-pinned let RHS of the SimpleStorage native dispatcher
equals the lowered `iszero(lt(calldatasize(), 4))` Yul expression that
`buildSwitch` emits. Combining the named-form decomposition
(`simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if`) with the
concrete-head exposure
(`simpleStorageNativeDispatcherInnerStmts_concrete_let_head`) and head
injection eliminates the structural existential between the named witness and
the concrete source expression, letting downstream proofs evaluate the let
RHS directly via the existing harness lemmas. -/
private theorem simpleStorageNativeDispatcher_letValue_eq :
    simpleStorageNativeDispatcher_letValue =
      Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.call "iszero"
          [Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [],
             Yul.YulExpr.lit 4]]) := by
  obtain ⟨_, hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_concrete_let_head
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.Let.injEq, Option.some.injEq,
    true_and] at hCombo
  exact hCombo.1

/-- The `Classical.choose`-pinned selector-miss guard condition of the
SimpleStorage native dispatcher equals the lowered `iszero(__has_selector)`
Yul expression that `buildSwitch` emits. Derived by head injection from the
concrete-form full equation and the named-form decomposition. -/
private theorem simpleStorageNativeDispatcher_if1Cond_eq :
    simpleStorageNativeDispatcher_if1Cond =
      Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.call "iszero"
          [Yul.YulExpr.ident "__has_selector"]) := by
  obtain ⟨_, _, hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_if
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact hCombo.2.1.1

/-- The `Classical.choose`-pinned selector-hit guard condition of the
SimpleStorage native dispatcher equals the lowered `__has_selector` ident
expression that `buildSwitch` emits. Derived by head injection from the
concrete-form full equation and the named-form decomposition. -/
private theorem simpleStorageNativeDispatcher_if2Cond_eq :
    simpleStorageNativeDispatcher_if2Cond =
      Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.ident "__has_selector") := by
  obtain ⟨_, _, hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_if
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact hCombo.2.2.1.1

/-- The `Classical.choose`-pinned selector-hit `If` body of the SimpleStorage
native dispatcher equals a singleton `lowerNativeSwitchBlock` over the
source-Yul `selectorExpr` (i.e., `shr(selectorShift, calldataload(0))`). The
switch-id, lowered case bodies, and lowered default body remain existential
because they depend on the concrete contract `functions` list — but their
existence as a closed-form switch block is enough to drive the next dispatcher
peel into selector-case dispatch. Derived by head injection from the
strengthened concrete-form `_eq_concrete_let_if_switchSingleton` and the
named-form decomposition. -/
private theorem simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_exists :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcher_if2Body =
        [Compiler.Proofs.YulGeneration.Backends.lowerNativeSwitchBlock
          (Yul.YulExpr.call "shr"
            [Yul.YulExpr.lit Compiler.Constants.selectorShift,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
          switchId cases' default'] := by
  obtain ⟨_, switchId, cases', default', hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact ⟨switchId, cases', default', hCombo.2.2.1.2⟩

/-- Strengthened companion of `simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_exists`:
the lowered default body of the dispatcher's selector-hit switch is pinned to
`[nativeRevertZeroZeroStmt]`. Derived by head injection from the strengthened
concrete-form `_eq_concrete_let_if_switchSingleton_revert_default` and the
named-form decomposition. -/
private theorem simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_revert_default_exists :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      simpleStorageNativeDispatcher_if2Body =
        [Compiler.Proofs.YulGeneration.Backends.lowerNativeSwitchBlock
          (Yul.YulExpr.call "shr"
            [Yul.YulExpr.lit Compiler.Constants.selectorShift,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
          switchId cases'
          [Backends.Native.nativeRevertZeroZeroStmt]] := by
  obtain ⟨_, switchId, cases', hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact ⟨switchId, cases', hCombo.2.2.1.2⟩

/-- Source-lowered companion of `_if2Body_eq_lowerSwitchBlock_revert_default_exists`:
the `if2Body` equality additionally exposes `switchId =
freshNativeSwitchId reservedNames n0` and the source-cases lowering equation
linking `simpleStorageBuildSwitchSourceCases` to the lowered `cases'`. This is
the form the dispatcher selector-miss closed-form consumes — chaining it with
`lowerSwitchCasesNativeWithSwitchIds_tags_eq` lifts source-level selector
facts through the lowering. -/
private theorem simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_revert_default_sourceLowered :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      simpleStorageNativeDispatcher_if2Body =
        [Compiler.Proofs.YulGeneration.Backends.lowerNativeSwitchBlock
          (Yul.YulExpr.call "shr"
            [Yul.YulExpr.lit Compiler.Constants.selectorShift,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
          (Backends.freshNativeSwitchId reservedNames n0) cases'
          [Backends.Native.nativeRevertZeroZeroStmt]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  obtain ⟨_, reservedNames, n0, cases', midN, hConcrete, hLowerCases⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default_sourceLowered
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact ⟨reservedNames, n0, cases', midN, hCombo.2.2.1.2, hLowerCases⟩

/-- The `Classical.choose`-pinned selector-miss `If` body of the SimpleStorage
native dispatcher equals the singleton list `[nativeRevertZeroZeroStmt]`.
Combines `simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if` with a
fully-pinned concrete-form decomposition of the inner block (where body1 is
also pinned via the WithSwitchIds revert lowering equation), then uses head
injection on the second `If` to extract the body equation. Lets downstream
selector-miss exec proofs invoke `exec_revert_zero_zero_error` directly. -/
private theorem simpleStorageNativeDispatcher_if1Body_eq :
    simpleStorageNativeDispatcher_if1Body =
      [Backends.Native.nativeRevertZeroZeroStmt] := by
  have hInner := simpleStorageNativeDispatcherInnerStmts_lowering_ok
  obtain ⟨rest', hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, rest'', hIf1, hBody1, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨body2', _, rest''', hIf2, _, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  have hDef :
      Compiler.CodegenCommon.defaultDispatchCase
          (none : Option Compiler.IREntrypoint)
          (none : Option Compiler.IREntrypoint) =
        [Yul.YulStmt.exprStmt
          (Yul.YulExpr.call "revert" [Yul.YulExpr.lit 0, Yul.YulExpr.lit 0])] :=
    rfl
  rw [hDef, lowerStmtsNativeWithSwitchIds_revert_zero_zero,
      Except.ok.injEq, Prod.mk.injEq] at hBody1
  obtain ⟨hBody1Eq, _⟩ := hBody1
  subst hBody1Eq
  rw [hIf2] at hIf1
  rw [hIf1] at hLet
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hLet
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact hCombo.2.1.2

/-- Closed-form selector-miss revert exec for the SimpleStorage native
dispatcher's first `If` body. The body is the singleton list
`[nativeRevertZeroZeroStmt]` (by `simpleStorageNativeDispatcher_if1Body_eq`),
so a `.Block` execution at any fuel `≥ 7` peels the head via
`exec_block_cons_error` and reduces to `exec_revert_zero_zero_error`,
producing EVMYulLean's `Revert` exception. Self-contained — no premise on
state/eval is needed because the body has no side effects before the revert.

This is the per-statement halt lemma the selector-miss dispatcher proof will
chain after the `let __has_selector := …` and `if iszero(__has_selector)`
peels: once `__has_selector = 0` is established, the if guard fires, and this
lemma immediately closes the dispatcher result as `.error Revert`. -/
private theorem exec_block_simpleStorageNativeDispatcher_if1Body_revert
    (fuel : Nat) (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.exec (fuel + 7) (.Block simpleStorageNativeDispatcher_if1Body)
        codeOverride state =
      .error EvmYul.Yul.Exception.Revert := by
  rw [simpleStorageNativeDispatcher_if1Body_eq]
  exact Compiler.Proofs.YulGeneration.Backends.Native.exec_block_cons_error
    (fuel + 6)
    Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt
    [] codeOverride state EvmYul.Yul.Exception.Revert
    (Compiler.Proofs.YulGeneration.Backends.Native.exec_revert_zero_zero_error
      fuel state codeOverride)

/-- Composed dispatcher peel exposing the SimpleStorage native dispatcher's
inner three-statement block exec as a singleton `lowerNativeSwitchBlock` exec
on the post-Let state. Chains the named let/if/if normalization with the
let-selector / if1-skip / if2-take peel
(`exec_block_letSelector_if1Skip_if2Take_initialState_fuel`, which discharges
calldatasize ≥ 4 via `hNoWrap` so the let binds `__has_selector` to 1) and the
just-landed `simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_exists`
characterization, leaving the dispatcher inner-block exec equal to a single
lowered switch-block exec on
`(nativeSwitchInitialOkState).insert "__has_selector" 1`. The switch-id,
lowered case bodies, and lowered default body remain existential — they are
fixed by the concrete `simpleStorageIRContract.functions` list and threaded
through later case-dispatch peels using
`exec_lowerNativeSwitchBlock_simpleStorageConcrete_*` lemmas. -/
private theorem exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_exec
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      EvmYul.Yul.exec (fuel + 12)
          (.Block simpleStorageNativeDispatcherInnerStmts)
          (some contract)
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            contract tx storage observableSlots ∅) =
        EvmYul.Yul.exec (fuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases' default'])
          (some contract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            contract tx storage observableSlots ∅).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
  obtain ⟨switchId, cases', default', hIf2Body⟩ :=
    simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_exists
  refine ⟨switchId, cases', default', ?_⟩
  rw [simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if,
      simpleStorageNativeDispatcher_letValue_eq,
      simpleStorageNativeDispatcher_if1Cond_eq,
      simpleStorageNativeDispatcher_if2Cond_eq, hIf2Body]
  exact Backends.Native.exec_block_letSelector_if1Skip_if2Take_postInitFreeMemory_fuel
    fuel contract tx storage observableSlots ∅ "__has_selector"
    simpleStorageNativeDispatcher_if1Body
    [Backends.lowerNativeSwitchBlock
      (Yul.YulExpr.call "shr"
        [Yul.YulExpr.lit Compiler.Constants.selectorShift,
         Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
      switchId cases' default']
    hNoWrap

/-- Strengthened companion of `exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_exec`
where the lowered default body of the inner switch is pinned to
`[nativeRevertZeroZeroStmt]`. Uses
`simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_revert_default_exists`
in place of the unpinned existential variant. -/
private theorem exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_revert_default_exec
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      EvmYul.Yul.exec (fuel + 12)
          (.Block simpleStorageNativeDispatcherInnerStmts)
          (some contract)
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            contract tx storage observableSlots ∅) =
        EvmYul.Yul.exec (fuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some contract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            contract tx storage observableSlots ∅).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
  obtain ⟨switchId, cases', hIf2Body⟩ :=
    simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_revert_default_exists
  refine ⟨switchId, cases', ?_⟩
  rw [simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if,
      simpleStorageNativeDispatcher_letValue_eq,
      simpleStorageNativeDispatcher_if1Cond_eq,
      simpleStorageNativeDispatcher_if2Cond_eq, hIf2Body]
  exact Backends.Native.exec_block_letSelector_if1Skip_if2Take_postInitFreeMemory_fuel
    fuel contract tx storage observableSlots ∅ "__has_selector"
    simpleStorageNativeDispatcher_if1Body
    [Backends.lowerNativeSwitchBlock
      (Yul.YulExpr.call "shr"
        [Yul.YulExpr.lit Compiler.Constants.selectorShift,
         Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
      switchId cases'
      [Backends.Native.nativeRevertZeroZeroStmt]]
    hNoWrap

/-- Source-lowered companion of `exec_block_..._eq_lowerNativeSwitchBlock_revert_default_exec`:
the inner-stmts-to-lowered-switch-block exec equation additionally exposes
`switchId = freshNativeSwitchId reservedNames n0` and the source-cases lowering
equation linking `simpleStorageBuildSwitchSourceCases` to the lowered `cases'`.
Built by switching the underlying `if2Body` decomposition to its sourceLowered
companion. -/
private theorem exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      EvmYul.Yul.exec (fuel + 12)
          (.Block simpleStorageNativeDispatcherInnerStmts)
          (some contract)
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            contract tx storage observableSlots ∅) =
        EvmYul.Yul.exec (fuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some contract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            contract tx storage observableSlots ∅).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  obtain ⟨reservedNames, n0, cases', midN, hIf2Body, hLowerCases⟩ :=
    simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_revert_default_sourceLowered
  refine ⟨reservedNames, n0, cases', midN, ?_, hLowerCases⟩
  rw [simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if,
      simpleStorageNativeDispatcher_letValue_eq,
      simpleStorageNativeDispatcher_if1Cond_eq,
      simpleStorageNativeDispatcher_if2Cond_eq, hIf2Body]
  exact Backends.Native.exec_block_letSelector_if1Skip_if2Take_postInitFreeMemory_fuel
    fuel contract tx storage observableSlots ∅ "__has_selector"
    simpleStorageNativeDispatcher_if1Body
    [Backends.lowerNativeSwitchBlock
      (Yul.YulExpr.call "shr"
        [Yul.YulExpr.lit Compiler.Constants.selectorShift,
         Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
      (Backends.freshNativeSwitchId reservedNames n0) cases'
      [Backends.Native.nativeRevertZeroZeroStmt]]
    hNoWrap

/-- Bridge-level lift of the inner-block-to-lowerNativeSwitchBlock combinator:
chains `simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec` with the
just-landed `_innerStmts_eq_lowerNativeSwitchBlock_exec`, so the bridge's
`contractDispatcherExecResult` at fuel `peeledFuel + 14` reduces to an exec of
a singleton lowered-switch block at fuel `peeledFuel + 8` on
`(initialOk).insert "__has_selector" 1`. -/
private theorem simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_exec
    (peeledFuel : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (peeledFuel + 15)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (peeledFuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases' default'])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots ∅).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
  obtain ⟨switchId, cases', default', hExec⟩ :=
    exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_exec
      peeledFuel Compiler.SimpleStorageNativeWitness.nativeContract
      tx storage observableSlots hNoWrap
  refine ⟨switchId, cases', default', ?_⟩
  have hShape : peeledFuel + 15 =
      Nat.succ (Nat.succ ((peeledFuel + 7) + 6)) := by omega
  rw [hShape, simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec
        (peeledFuel + 7) tx storage observableSlots]
  exact hExec

/-- Strengthened companion of `simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_exec`
with the lowered default body pinned to `[nativeRevertZeroZeroStmt]`. Chains
the `_innerBlock_exec` combinator with the strengthened
`_innerStmts_eq_lowerNativeSwitchBlock_revert_default_exec`. This is the entry
point that downstream selector-miss bridge proofs will plug into the new
store-parametric `exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_fuel`
endpoint. -/
private theorem simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec
    (peeledFuel : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (peeledFuel + 15)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (peeledFuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots ∅).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
  obtain ⟨switchId, cases', hExec⟩ :=
    exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_revert_default_exec
      peeledFuel Compiler.SimpleStorageNativeWitness.nativeContract
      tx storage observableSlots hNoWrap
  refine ⟨switchId, cases', ?_⟩
  have hShape : peeledFuel + 15 =
      Nat.succ (Nat.succ ((peeledFuel + 7) + 6)) := by omega
  rw [hShape, simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec
        (peeledFuel + 7) tx storage observableSlots]
  exact hExec

/-- Source-lowered companion of `_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec`:
the dispatcher-level reduction additionally exposes
`switchId = freshNativeSwitchId reservedNames n0` and the source-cases lowering
equation. This is the form selector-miss closed-form proofs will consume —
they open the existential, then chain `lowerSwitchCasesNativeWithSwitchIds_tags_eq`
to lift source-level selector facts (decided from `simpleStorageIRContract`)
into the lowered `cases'.find?` results required by the `_via_reduction`
endpoint. -/
private theorem simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
    (peeledFuel : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (peeledFuel + 15)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (peeledFuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots ∅).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      peeledFuel Compiler.SimpleStorageNativeWitness.nativeContract
      tx storage observableSlots hNoWrap
  refine ⟨reservedNames, n0, cases', midN, ?_, hLowerCases⟩
  have hShape : peeledFuel + 15 =
      Nat.succ (Nat.succ ((peeledFuel + 7) + 6)) := by omega
  rw [hShape, simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec
        (peeledFuel + 7) tx storage observableSlots]
  exact hExec

/-- Bridge-level selector-miss endpoint, parametric in `cases'` and `switchId`:
composes the harness-level
`exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error` with
the strengthened-reduction equation at the matching fuel
`peeledFuel = fuel + cases'.length + 5`. The reduction equation is taken as a
hypothesis so the caller can pin a specific `cases'` (e.g. by opening the
existential of `_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec`)
without forcing the fuel parameter to depend on a not-yet-bound term. This is
the direct selector-miss discharge composing into
`contractDispatcherExecResult = .error Revert`. -/
private theorem simpleStorageNativeContract_dispatcherExec_selectorMiss_revert_via_reduction
    (fuel selector switchId : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFind : cases'.find? (fun entry => entry.1 == selector) = none)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size)
    (hReduction :
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (fuel + cases'.length + 20)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots ∅).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1))) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + cases'.length + 20)
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  rw [hReduction]
  exact (Backends.Native.exec_block_lowerNativeSwitchBlock_revert_default_postInitFreeMemory_hasSelectorState_projectResult_eq
    fuel selector switchId cases'
    Compiler.SimpleStorageNativeWitness.nativeContract
    tx storage [] observableSlots hSelector hFind hSelectorRange hTagsRange).1

/-- The source-level switch cases emitted by `buildSwitch` for SimpleStorage
project to the concrete two-element selector list `[0x6057361d, 0x2e64cec1]`.
This anchors source-level selector-miss reasoning at the IR layer so the rest
of the dispatcher proof can stay parametric in `cases'`. -/
private theorem simpleStorageBuildSwitchSourceCases_map_fst :
    simpleStorageBuildSwitchSourceCases.map (·.1) =
      [(0x6057361d : Nat), (0x2e64cec1 : Nat)] := rfl

/-- Source-cases find?-none for SimpleStorage: the selector-miss assumption
`sel ≠ 0x6057361d ∧ sel ≠ 0x2e64cec1` (the two SimpleStorage IR selectors)
suffices to discharge `find?` on the buildSwitch-emitted source case list.
This is the source-level half of the selector-miss closed form. -/
private theorem simpleStorageBuildSwitchSourceCases_find?_none {sel : Nat}
    (h1 : sel ≠ 0x6057361d) (h2 : sel ≠ 0x2e64cec1) :
    simpleStorageBuildSwitchSourceCases.find? (fun entry => entry.1 == sel) =
      none := by
  show ([_, _] : List _).find? _ = none
  simp only [List.find?_cons, List.find?_nil]
  have hb1 : ((0x6057361d : Nat) == sel) = false :=
    beq_eq_false_iff_ne.mpr (Ne.symm h1)
  have hb2 : ((0x2e64cec1 : Nat) == sel) = false :=
    beq_eq_false_iff_ne.mpr (Ne.symm h2)
  rw [hb1, hb2]

/-- All tags in the buildSwitch-emitted source cases for SimpleStorage are
strictly less than `EvmYul.UInt256.size = 2^256`. The two source selectors
(`0x6057361d`, `0x2e64cec1`) both fit in 32 bits, far below the EVM word
modulus. -/
private theorem simpleStorageBuildSwitchSourceCases_tags_lt_uint256_size :
    ∀ tag body, (tag, body) ∈ simpleStorageBuildSwitchSourceCases →
      tag < EvmYul.UInt256.size := by
  intro tag body h
  simp only [simpleStorageBuildSwitchSourceCases, simpleStorageIRContract,
    List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

/-- Shape characterization for the lowered SimpleStorage source switch cases.

Exactly two entries — the SimpleStorage IR selectors `0x6057361d` and
`0x2e64cec1` — flow through `lowerSwitchCasesNativeWithSwitchIds`, so the
output `cases'` is forced to a two-element shape with lowered bodies. Each
selector tag is preserved unchanged by the lowering; only the case bodies
are recursively lowered. Hit-case proofs consume this shape to convert the
parametric `cases'` (opened from the `_sourceLowered` existential) into the
concrete `[(0x6057361d, _), (0x2e64cec1, _)]` form that matches the
generic harness lemmas like
`exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_error_fuel`. -/
private theorem simpleStorageBuildSwitchSourceCases_lowered_shape
    (reservedNames : List String) (nextSwitchId final : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower :
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId
        simpleStorageBuildSwitchSourceCases = .ok (cases', final)) :
    ∃ storeBody' retrieveBody',
      cases' = [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')] := by
  have hTags := Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq
    _ _ _ _ _ hLower
  have hLen := Backends.lowerSwitchCasesNativeWithSwitchIds_length_eq
    _ _ _ _ _ hLower
  rw [simpleStorageBuildSwitchSourceCases_map_fst] at hTags
  match cases', hLen, hTags with
  | [(t1, b1), (t2, b2)], _, hTags =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hTags
    obtain ⟨ht1, ht2⟩ := hTags
    exact ⟨b1, b2, by rw [ht1, ht2]⟩

/-- Lowered native body shape of the `store(uint256)` selector arm of the
SimpleStorage source switch cases (leading `.Block []` from the `dispatchBody`
comment, followed by callvalue/calldatasize guards and the calldataload/
sstore/stop primitive sequence). Pinning this lets downstream hit-case proofs
specialize to a fixed concrete body instead of carrying a parametric
`storeBody'`. -/
private def simpleStorageLoweredStoreCaseBody : List EvmYul.Yul.Ast.Stmt :=
  [EvmYul.Yul.Ast.Stmt.Block [],
   .If (Backends.lowerExprNative (.call "callvalue" []))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 36]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .Let ["value"] (some (Backends.lowerExprNative
     (.call "calldataload" [.lit 4]))),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "sstore" [.lit 0, .ident "value"])),
   .ExprStmtCall (Backends.lowerExprNative (.call "stop" []))]

/-- Lowered native body shape of the `retrieve()` selector arm of the
SimpleStorage source switch cases. Mirrors `simpleStorageLoweredStoreCaseBody`
for the source `mstore(0, sload(0)); return(0, 32)` body. -/
private def simpleStorageLoweredRetrieveCaseBody : List EvmYul.Yul.Ast.Stmt :=
  [EvmYul.Yul.Ast.Stmt.Block [],
   .If (Backends.lowerExprNative (.call "callvalue" []))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 4]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0, .call "sload" [.lit 0]])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

/-- 5-statement tail of `simpleStorageLoweredStoreCaseBody`, with the leading
no-op `.Block []` (from the `dispatchBody` source comment) stripped. -/
private def simpleStorageLoweredStoreCaseBodyTail : List EvmYul.Yul.Ast.Stmt :=
  [.If (Backends.lowerExprNative (.call "callvalue" []))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 36]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .Let ["value"] (some (Backends.lowerExprNative
     (.call "calldataload" [.lit 4]))),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "sstore" [.lit 0, .ident "value"])),
   .ExprStmtCall (Backends.lowerExprNative (.call "stop" []))]

/-- 4-statement tail of `simpleStorageLoweredRetrieveCaseBody`, with the leading
no-op `.Block []` (from the `dispatchBody` source comment) stripped. -/
private def simpleStorageLoweredRetrieveCaseBodyTail : List EvmYul.Yul.Ast.Stmt :=
  [.If (Backends.lowerExprNative (.call "callvalue" []))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 4]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0, .call "sload" [.lit 0]])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

/-- Strip the leading `.Block []` no-op (a `dispatchBody` source-comment
artifact) from the lowered store-case body when proving a `.error err`
obligation. Combines `exec_block_nil_ok` (the empty inner block is a no-op at
positive fuel, returning the input state unchanged) with
`exec_block_cons_tail_error` (a successful head followed by an erroring tail
makes the whole block error). Reduces a 6-statement obligation to a strictly
smaller 5-statement tail obligation. -/
private theorem exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error
    (fuel' : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) (err : EvmYul.Yul.Exception)
    (hTail :
      EvmYul.Yul.exec (fuel' + 1)
        (.Block simpleStorageLoweredStoreCaseBodyTail) codeOverride state =
        .error err) :
    EvmYul.Yul.exec (fuel' + 2)
      (.Block simpleStorageLoweredStoreCaseBody) codeOverride state =
      .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel' + 1))
    (.Block (.Block [] :: simpleStorageLoweredStoreCaseBodyTail))
    codeOverride state = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel' + 1) (.Block [])
    simpleStorageLoweredStoreCaseBodyTail codeOverride state state err ?_ hTail
  exact Backends.Native.exec_block_nil_ok fuel' codeOverride state

/-- Retrieve-case dual of
`exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error`. -/
private theorem exec_block_simpleStorageLoweredRetrieveCaseBody_head_strip_error
    (fuel' : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) (err : EvmYul.Yul.Exception)
    (hTail :
      EvmYul.Yul.exec (fuel' + 1)
        (.Block simpleStorageLoweredRetrieveCaseBodyTail) codeOverride state =
        .error err) :
    EvmYul.Yul.exec (fuel' + 2)
      (.Block simpleStorageLoweredRetrieveCaseBody) codeOverride state =
      .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel' + 1))
    (.Block (.Block [] :: simpleStorageLoweredRetrieveCaseBodyTail))
    codeOverride state = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel' + 1) (.Block [])
    simpleStorageLoweredRetrieveCaseBodyTail codeOverride state state err ?_ hTail
  exact Backends.Native.exec_block_nil_ok fuel' codeOverride state

/-- 4-statement callvalue-stripped tail of `simpleStorageLoweredStoreCaseBody`,
with both the leading no-op `.Block []` and the leading `if callvalue() {…}`
revert guard removed. Used to further shrink the dispatcher hit-case body-exec
obligation when the transaction has zero `msgValue`. -/
private def simpleStorageLoweredStoreCaseBodyTail2 : List EvmYul.Yul.Ast.Stmt :=
  [.If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 36]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .Let ["value"] (some (Backends.lowerExprNative
     (.call "calldataload" [.lit 4]))),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "sstore" [.lit 0, .ident "value"])),
   .ExprStmtCall (Backends.lowerExprNative (.call "stop" []))]

/-- 3-statement calldatasize-stripped tail of
`simpleStorageLoweredStoreCaseBodyTail2`, with the argument-length revert guard
removed after proving the transaction supplies the setter argument. -/
private def simpleStorageLoweredStoreCaseBodyTail3 : List EvmYul.Yul.Ast.Stmt :=
  [.Let ["value"] (some (Backends.lowerExprNative
     (.call "calldataload" [.lit 4]))),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "sstore" [.lit 0, .ident "value"])),
   .ExprStmtCall (Backends.lowerExprNative (.call "stop" []))]

private theorem nativeSwitchPostInitFreeMemorySharedState_weiValue
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).executionEnv.weiValue =
      Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 tx.msgValue := by
  simp [Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    Compiler.Proofs.YulGeneration.Backends.Native.initialState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
    YulState.initial, EvmYul.Yul.State.sharedState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.mkBlockHeader]

private theorem nativeSwitchPostInitFreeMemorySharedState_calldata_size
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).executionEnv.calldata.size =
      4 + tx.args.length * 32 := by
  simp [Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    Compiler.Proofs.YulGeneration.Backends.Native.initialState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
    YulState.initial, EvmYul.Yul.State.sharedState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.mkBlockHeader,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.calldataToByteArray_size]

private theorem nativeSwitchPostInitFreeMemorySharedState_perm
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).executionEnv.perm = true := by
  simp [Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    Compiler.Proofs.YulGeneration.Backends.Native.initialState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
    YulState.initial, EvmYul.Yul.State.sharedState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.mkBlockHeader]

/-- Closed-form native exec of the direct lowered setter body from the
generated dispatcher marked-prefix state.

This is the direct-body counterpart of the SimpleStorage hit-case theorem below:
it works for any lowered native contract and any switch temporary store because
the body reads calldata and writes storage through the shared state. -/
private theorem exec_block_store0_calldataload4_stop_markedPrefix_halt
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest) :
    let initialWithStore :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
        contract tx storage observableSlots switchId store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    EvmYul.Yul.exec (fuel + 10)
        (.Block simpleStorageLoweredStoreCaseBodyTail3)
        (some contract) initialWithStore =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  intro initialWithStore withValue finalState
  have hWord :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        contract tx storage observableSlots).sharedState.calldataload
          (EvmYul.UInt256.ofNat 4) =
        Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg := by
    simpa [Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      EvmYul.Yul.State.sharedState, EvmYul.Yul.State.toState] using
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataload4_arg0_word
        contract tx storage observableSlots arg rest hArgs
  simp [simpleStorageLoweredStoreCaseBodyTail3, Backends.lowerExprNative,
    Backends.lookupRuntimePrimOp_calldataload, Backends.lookupRuntimePrimOp_sstore,
    Backends.lookupRuntimePrimOp_stop, EvmYul.Yul.exec, EvmYul.Yul.eval,
    EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.State.multifill, initialWithStore, withValue, finalState,
    hWord,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv]
  cases withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg) <;>
    rfl

/-- 3-statement callvalue-stripped tail of `simpleStorageLoweredRetrieveCaseBody`. -/
private def simpleStorageLoweredRetrieveCaseBodyTail2 : List EvmYul.Yul.Ast.Stmt :=
  [.If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 4]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0, .call "sload" [.lit 0]])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

/-- 2-statement lt-calldatasize-stripped tail of
`simpleStorageLoweredRetrieveCaseBodyTail2`, with both the callvalue revert
guard and the inner `if lt(calldatasize, 4) {…}` argument-length revert
guard removed. Used to further shrink the dispatcher hit-case body-exec
obligation when the calldata is at least 4 bytes (which is automatic for any
ABI-conforming call since the selector itself is 4 bytes). -/
private def simpleStorageLoweredRetrieveCaseBodyTail3 : List EvmYul.Yul.Ast.Stmt :=
  [.ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0, .call "sload" [.lit 0]])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

private def loweredLiteralReturnCaseBodyTail (value : Nat) :
    List EvmYul.Yul.Ast.Stmt :=
  [.ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0, .lit value])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

private def loweredZeroParamLiteralReturnCaseBody (value : Nat) :
    List EvmYul.Yul.Ast.Stmt :=
  .If (Backends.lowerExprNative
        (.call "lt" [.call "calldatasize" [], .lit 4]))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))] ::
    loweredLiteralReturnCaseBodyTail value

private def loweredZeroParamSload0ReturnCaseBody :
    List EvmYul.Yul.Ast.Stmt :=
  .If (Backends.lowerExprNative
        (.call "lt" [.call "calldatasize" [], .lit 4]))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))] ::
    simpleStorageLoweredRetrieveCaseBodyTail3

private def loweredCalldataload4ReturnCaseBodyTail :
    List EvmYul.Yul.Ast.Stmt :=
  [.ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0, .call "calldataload" [.lit 4]])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

private def loweredCalldataloadReturnCaseBodyTail (idx : Nat) :
    List EvmYul.Yul.Ast.Stmt :=
  [.ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0,
       .call "calldataload" [.lit (4 + 32 * idx)]])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

/-- Strip the leading `if callvalue() { revert(0,0) }` guard from
`simpleStorageLoweredStoreCaseBodyTail` when proving a `.error err`
obligation, given that the current `executionEnv.weiValue` is zero (the
canonical zero literal). Combines the harness skip lemma
`exec_if_lowerExprNative_callvalue_skip_zero_fuel` (the callvalue guard
is a no-op at zero `weiValue`) with `exec_block_cons_tail_error` (a
successful head followed by an erroring tail makes the whole block
error). Reduces a 5-statement tail obligation to a 4-statement
callvalue-stripped tail2 obligation. -/
private theorem exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hWei : shared.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal))
    (hTail2 :
      EvmYul.Yul.exec (fuel + 7) (.Block simpleStorageLoweredStoreCaseBodyTail2)
        codeOverride (.Ok shared store) = .error err) :
    EvmYul.Yul.exec (fuel + 8) (.Block simpleStorageLoweredStoreCaseBodyTail)
      codeOverride (.Ok shared store) = .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 7))
    (.Block ((simpleStorageLoweredStoreCaseBodyTail).head! ::
      simpleStorageLoweredStoreCaseBodyTail2))
    codeOverride (.Ok shared store) = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel + 7) _
    simpleStorageLoweredStoreCaseBodyTail2 codeOverride
    (.Ok shared store) (.Ok shared store) err ?_ hTail2
  show EvmYul.Yul.exec ((fuel + 1) + 6)
    (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))])
    codeOverride (.Ok shared store) = .ok (.Ok shared store)
  exact Backends.Native.exec_if_lowerExprNative_callvalue_skip_zero_fuel
    (fuel + 1) _ codeOverride shared store hWei

/-- Retrieve-case dual of
`exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error`. -/
private theorem exec_block_simpleStorageLoweredRetrieveCaseBodyTail_callvalue_strip_error
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hWei : shared.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal))
    (hTail2 :
      EvmYul.Yul.exec (fuel + 6)
        (.Block simpleStorageLoweredRetrieveCaseBodyTail2)
        codeOverride (.Ok shared store) = .error err) :
    EvmYul.Yul.exec (fuel + 7) (.Block simpleStorageLoweredRetrieveCaseBodyTail)
      codeOverride (.Ok shared store) = .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 6))
    (.Block ((simpleStorageLoweredRetrieveCaseBodyTail).head! ::
      simpleStorageLoweredRetrieveCaseBodyTail2))
    codeOverride (.Ok shared store) = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel + 6) _
    simpleStorageLoweredRetrieveCaseBodyTail2 codeOverride
    (.Ok shared store) (.Ok shared store) err ?_ hTail2
  show EvmYul.Yul.exec ((fuel) + 6)
    (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))])
    codeOverride (.Ok shared store) = .ok (.Ok shared store)
  exact Backends.Native.exec_if_lowerExprNative_callvalue_skip_zero_fuel
    fuel _ codeOverride shared store hWei

/-- Strip the leading `if lt(calldatasize(), 4) { revert(0,0) }` argument-length
guard from `simpleStorageLoweredRetrieveCaseBodyTail2` when proving a
`.error err` obligation, given that the current calldata has at least 4
bytes (the selector). Combines the harness skip lemma
`exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel` with
`exec_block_cons_tail_error`. Reduces a 3-statement tail2 obligation to a
2-statement lt-stripped tail3 obligation. -/
private theorem exec_block_simpleStorageLoweredRetrieveCaseBodyTail2_lt_strip_error
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 4 ≤ shared.executionEnv.calldata.size)
    (hTail3 :
      EvmYul.Yul.exec (fuel + 9)
        (.Block simpleStorageLoweredRetrieveCaseBodyTail3)
        codeOverride (.Ok shared store) = .error err) :
    EvmYul.Yul.exec (fuel + 10)
      (.Block simpleStorageLoweredRetrieveCaseBodyTail2)
      codeOverride (.Ok shared store) = .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 9))
    (.Block ((simpleStorageLoweredRetrieveCaseBodyTail2).head! ::
      simpleStorageLoweredRetrieveCaseBodyTail3))
    codeOverride (.Ok shared store) = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel + 9) _
    simpleStorageLoweredRetrieveCaseBodyTail3 codeOverride
    (.Ok shared store) (.Ok shared store) err ?_ hTail3
  show EvmYul.Yul.exec (fuel + 9)
    (.If (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit 4]))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))])
    codeOverride (.Ok shared store) = .ok (.Ok shared store)
  exact Backends.Native.exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel
    fuel _ codeOverride shared store 4 hSize (by decide) hGe

/-- Store-case dual of
`exec_block_simpleStorageLoweredRetrieveCaseBodyTail2_lt_strip_error`, with
the ABI argument guard threshold `36 = 4 + 32`. -/
private theorem exec_block_simpleStorageLoweredStoreCaseBodyTail2_lt_strip_error
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 36 ≤ shared.executionEnv.calldata.size)
    (hTail3 :
      EvmYul.Yul.exec (fuel + 10)
        (.Block simpleStorageLoweredStoreCaseBodyTail3)
        codeOverride (.Ok shared store) = .error err) :
    EvmYul.Yul.exec (fuel + 11)
      (.Block simpleStorageLoweredStoreCaseBodyTail2)
      codeOverride (.Ok shared store) = .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 10))
    (.Block ((simpleStorageLoweredStoreCaseBodyTail2).head! ::
      simpleStorageLoweredStoreCaseBodyTail3))
    codeOverride (.Ok shared store) = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel + 10) _
    simpleStorageLoweredStoreCaseBodyTail3 codeOverride
    (.Ok shared store) (.Ok shared store) err ?_ hTail3
  show EvmYul.Yul.exec (fuel + 10)
    (.If (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit 36]))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))])
    codeOverride (.Ok shared store) = .ok (.Ok shared store)
  exact Backends.Native.exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel
    (fuel + 1) _ codeOverride shared store 36 hSize (by decide) hGe

/-- Closed-form native exec of the store payload
`let value := calldataload(4); sstore(0, value); stop` for an arbitrary
shared state/store once the calldata word is known. -/
private theorem exec_block_store0_calldataload4_stop_shared_halt
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (hPerm : shared.executionEnv.perm = true)
    (hWord :
      shared.calldataload (EvmYul.UInt256.ofNat 4) =
        Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg) :
    let initialWithStore : EvmYul.Yul.State := .Ok shared store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    EvmYul.Yul.exec (fuel + 10)
        (.Block simpleStorageLoweredStoreCaseBodyTail3)
        codeOverride initialWithStore =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  intro initialWithStore withValue finalState
  simp [simpleStorageLoweredStoreCaseBodyTail3, Backends.lowerExprNative,
    Backends.lookupRuntimePrimOp_calldataload, Backends.lookupRuntimePrimOp_sstore,
    Backends.lookupRuntimePrimOp_stop, EvmYul.Yul.exec, EvmYul.Yul.eval,
    EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.State.multifill, initialWithStore, withValue, finalState,
    hWord, EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]
  have hPerm :
      (EvmYul.Yul.State.Ok shared
        (Finmap.insert "value"
          (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
          store)).executionEnv.perm = true := by
    simpa [EvmYul.Yul.State.executionEnv] using hPerm
  rw [show fuel + 7 = (fuel + 6) + 1 by omega]
  rw [Compiler.Proofs.YulGeneration.Backends.Native.primCall_sstore_ok
    (fuel + 6) _ _ _ hPerm]
  rfl

private theorem exec_block_store0_calldataload4_stop_shared_halt_tight
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (hPerm : shared.executionEnv.perm = true)
    (hWord :
      shared.calldataload (EvmYul.UInt256.ofNat 4) =
        Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg) :
    let initialWithStore : EvmYul.Yul.State := .Ok shared store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    EvmYul.Yul.exec (fuel + 9)
        (.Block simpleStorageLoweredStoreCaseBodyTail3)
        codeOverride initialWithStore =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  intro initialWithStore withValue finalState
  simp [simpleStorageLoweredStoreCaseBodyTail3, Backends.lowerExprNative,
    Backends.lookupRuntimePrimOp_calldataload, Backends.lookupRuntimePrimOp_sstore,
    Backends.lookupRuntimePrimOp_stop, EvmYul.Yul.exec, EvmYul.Yul.eval,
    EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.State.multifill, initialWithStore, withValue, finalState,
    hWord, EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]
  have hPerm' :
      (EvmYul.Yul.State.Ok shared
        (Finmap.insert "value"
          (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
          store)).executionEnv.perm = true := by
    simpa [EvmYul.Yul.State.executionEnv] using hPerm
  rw [show fuel + 6 = (fuel + 5) + 1 by omega]
  rw [Compiler.Proofs.YulGeneration.Backends.Native.primCall_sstore_ok
    (fuel + 5) _ _ _ hPerm']
  rfl

private theorem exec_block_simpleStorageLoweredStoreCaseBodyTail2_lt_strip_error_tight
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 36 ≤ shared.executionEnv.calldata.size)
    (hTail3 :
      EvmYul.Yul.exec (fuel + 9)
        (.Block simpleStorageLoweredStoreCaseBodyTail3)
        codeOverride (.Ok shared store) = .error err) :
    EvmYul.Yul.exec (fuel + 10)
      (.Block simpleStorageLoweredStoreCaseBodyTail2)
      codeOverride (.Ok shared store) = .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 9))
    (.Block ((simpleStorageLoweredStoreCaseBodyTail2).head! ::
      simpleStorageLoweredStoreCaseBodyTail3))
    codeOverride (.Ok shared store) = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel + 9) _
    simpleStorageLoweredStoreCaseBodyTail3 codeOverride
    (.Ok shared store) (.Ok shared store) err ?_ hTail3
  show EvmYul.Yul.exec (fuel + 9)
    (.If (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit 36]))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))])
    codeOverride (.Ok shared store) = .ok (.Ok shared store)
  exact Backends.Native.exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel
    fuel _ codeOverride shared store 36 hSize (by decide) hGe

/-- Closed-form native exec of the generated one-argument setter body from the
generated dispatcher marked-prefix state. -/
private theorem exec_block_simpleStorageLoweredStoreCaseBodyTail2_markedPrefix_halt
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    let markedStore :=
      (((store.insert (Backends.nativeSwitchDiscrTempName switchId)
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1))
    let shared :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        contract tx storage observableSlots
    let initialWithStore : EvmYul.Yul.State := .Ok shared markedStore
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    EvmYul.Yul.exec (fuel + 10)
        (.Block simpleStorageLoweredStoreCaseBodyTail2)
        (some contract) initialWithStore =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  intro markedStore shared initialWithStore withValue finalState
  have hWord :
      shared.calldataload (EvmYul.UInt256.ofNat 4) =
        Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg := by
    simpa [shared,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      EvmYul.Yul.State.sharedState, EvmYul.Yul.State.toState] using
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataload4_arg0_word
        contract tx storage observableSlots arg rest hArgs
  have hTail3 :
      EvmYul.Yul.exec (fuel + 9)
          (.Block simpleStorageLoweredStoreCaseBodyTail3)
          (some contract) initialWithStore =
        .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
    have hPerm : shared.executionEnv.perm = true := by
      simp [shared,
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
        Compiler.Proofs.YulGeneration.Backends.Native.initialState,
        Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
        YulState.initial, EvmYul.Yul.State.sharedState]
    simpa [initialWithStore, withValue, finalState] using
      exec_block_store0_calldataload4_stop_shared_halt_tight
        fuel (some contract) shared markedStore arg hPerm hWord
  have hCalldataSize :
      shared.executionEnv.calldata.size = 4 + tx.args.length * 32 := by
    simpa [shared,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.Yul.State.sharedState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.calldataToByteArray_size]
  have hSize :
      shared.executionEnv.calldata.size < EvmYul.UInt256.size := by
    simpa [hCalldataSize] using hNoWrap
  have hGe :
      36 ≤ shared.executionEnv.calldata.size := by
    rw [hCalldataSize, hArgs]
    simp
    omega
  simpa [initialWithStore] using
    exec_block_simpleStorageLoweredStoreCaseBodyTail2_lt_strip_error_tight
      fuel (some contract) shared markedStore
      (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) hSize hGe hTail3

/-- Store-case argument-length guard fires when calldata contains only the
selector. This is the short-calldata counterpart to
`exec_block_simpleStorageLoweredStoreCaseBodyTail2_lt_strip_error`. -/
private theorem exec_block_simpleStorageLoweredStoreCaseBodyTail2_short_revert
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hSizeEq : shared.executionEnv.calldata.size = 4) :
    EvmYul.Yul.exec (fuel + 11)
      (.Block simpleStorageLoweredStoreCaseBodyTail2)
      codeOverride (.Ok shared store) =
      .error EvmYul.Yul.Exception.Revert := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 10))
    (.Block ((simpleStorageLoweredStoreCaseBodyTail2).head! ::
      simpleStorageLoweredStoreCaseBodyTail3))
    codeOverride (.Ok shared store) = .error EvmYul.Yul.Exception.Revert
  refine Backends.Native.exec_block_cons_error (fuel + 10) _
    simpleStorageLoweredStoreCaseBodyTail3 codeOverride
    (.Ok shared store) EvmYul.Yul.Exception.Revert ?_
  refine Backends.Native.exec_if_eval_nonzero_error (fuel + 9) _ _
    codeOverride (.Ok shared store) (.Ok shared store)
    (EvmYul.UInt256.ofNat 1) EvmYul.Yul.Exception.Revert ?_ ?_ ?_
  · rw [Backends.Native.eval_lowerExprNative_lt_calldatasize_ok_fuel]
    simp [hSizeEq, EvmYul.UInt256.lt, EvmYul.UInt256.ofNat, Fin.ofNat,
      EvmYul.UInt256.size]
    decide
  · change (EvmYul.UInt256.ofNat 1 : EvmYul.UInt256) ≠ ⟨0⟩
    decide
  · simpa [Backends.Native.nativeRevertZeroZeroStmt, Backends.lowerExprNative,
      Backends.lookupRuntimePrimOp_revert] using
      (Backends.Native.exec_block_cons_error (fuel + 8)
      Backends.Native.nativeRevertZeroZeroStmt [] codeOverride
      (.Ok shared store) EvmYul.Yul.Exception.Revert
      (Backends.Native.exec_revert_zero_zero_error (fuel + 2)
        (.Ok shared store) codeOverride))

/-- Closed-form native exec of the store hit-case 3-statement payload
    `let value := calldataload(4); sstore(0, value); stop` after the
    callvalue and argument-length guards have been stripped. -/
private theorem exec_block_simpleStorageLoweredStoreCaseBodyTail3_halt
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (store : EvmYul.Yul.VarStore)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest) :
    let initialWithStore : EvmYul.Yul.State :=
      .Ok (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    EvmYul.Yul.exec (fuel + 10)
        (.Block simpleStorageLoweredStoreCaseBodyTail3)
        codeOverride initialWithStore =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  intro initialWithStore withValue finalState
  have hWord :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.calldataload (EvmYul.UInt256.ofNat 4) =
        Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg := by
    simpa [Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      EvmYul.Yul.State.sharedState, EvmYul.Yul.State.toState] using
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataload4_arg0_word
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage observableSlots
        arg rest hArgs
  simp [simpleStorageLoweredStoreCaseBodyTail3, Backends.lowerExprNative,
    Backends.lookupRuntimePrimOp_calldataload, Backends.lookupRuntimePrimOp_sstore,
    Backends.lookupRuntimePrimOp_stop, EvmYul.Yul.exec, EvmYul.Yul.eval,
    EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.State.multifill, initialWithStore, withValue, finalState,
    hWord, EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]
  have hPerm :
      (EvmYul.Yul.State.Ok
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots).sharedState
        (Finmap.insert "value"
          (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
          store)).executionEnv.perm = true := by
    rfl
  rw [show fuel + 7 = (fuel + 6) + 1 by omega]
  rw [Compiler.Proofs.YulGeneration.Backends.Native.primCall_sstore_ok
    (fuel + 6) _ _ _ hPerm]
  rfl

/-- Composed body-level closed form for the SimpleStorage store hit-case when
the calldata contains the setter argument. -/
private theorem exec_block_simpleStorageLoweredStoreCaseBody_halt
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (store : EvmYul.Yul.VarStore)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest)
    (hPerm : shared.executionEnv.perm = true)
    (hWord :
      shared.calldataload (EvmYul.UInt256.ofNat 4) =
        Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    (hWei : shared.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal))
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 36 ≤ shared.executionEnv.calldata.size) :
    let initialWithStore : EvmYul.Yul.State :=
      .Ok shared store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    EvmYul.Yul.exec (fuel + 13) (.Block simpleStorageLoweredStoreCaseBody)
        codeOverride initialWithStore =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  intro initialWithStore withValue finalState
  have hTail3 := exec_block_store0_calldataload4_stop_shared_halt
    fuel codeOverride shared store arg hPerm hWord
  have hTail2 := exec_block_simpleStorageLoweredStoreCaseBodyTail2_lt_strip_error
    fuel codeOverride shared store _ hSize hGe hTail3
  have hTail := exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error
    (fuel + 4) codeOverride shared store _ hWei hTail2
  exact exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error
    (fuel + 11) codeOverride initialWithStore _ hTail

/-- Closed-form native exec of the retrieve hit-case 2-statement payload
    `mstore(0, sload(0)) ; return(0, 32)`. EVMYulLean models `RETURN` as a
    halt error; the exec composes the harness's exec-side
    `mstore(lit, sload(lit))` seam with the exec-side `return(lit, lit)`
    halt seam through `exec_block_cons_tail_error`. The resulting halt state
    threads (i) storage-access tracking from the SLOAD on slot zero,
    (ii) the memory write of the loaded word at offset zero, and
    (iii) the post-`evmReturn` machine state holding the 32-byte return
    buffer. Discharges the `hTail3` premise of
    `exec_block_simpleStorageLoweredRetrieveCaseBodyTail2_lt_strip_error`
    unconditionally — no extra calldata/wei hypotheses needed because the
    payload reads only from storage and writes only to memory. -/
private theorem exec_block_simpleStorageLoweredRetrieveCaseBodyTail3_closed
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.exec (fuel + 9)
        (.Block simpleStorageLoweredRetrieveCaseBodyTail3)
        codeOverride (.Ok shared store) =
      let (state', value) := shared.sload (EvmYul.UInt256.ofNat 0)
      let shared1 : EvmYul.SharedState .Yul := { shared with toState := state' }
      let shared2 : EvmYul.SharedState .Yul :=
        { shared1 with
          toMachineState :=
            shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
      let shared3 : EvmYul.SharedState .Yul :=
        { shared2 with
          toMachineState :=
            shared2.toMachineState.evmReturn
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
      .error (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store) ⟨1⟩) := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 8))
    (.Block ((simpleStorageLoweredRetrieveCaseBodyTail3).head! ::
      [(simpleStorageLoweredRetrieveCaseBodyTail3).getLast!]))
    codeOverride (.Ok shared store) = _
  refine Backends.Native.exec_block_cons_tail_error (fuel + 8) _ _ codeOverride
    (.Ok shared store) _ _
    (Backends.Native.exec_lowerExprNative_mstore_lit_sload_lit_ok_fuel
      fuel shared store codeOverride 0 0) ?_
  -- Tail [return(0, 32)] errors via the singleton-return harness lemma.
  have hSeam :=
    Backends.Native.exec_block_singleton_lowerExprNative_return_lit_lit_error_fuel
      (fuel + 1)
      ({ ({ shared with toState := (shared.sload (EvmYul.UInt256.ofNat 0)).1 }
            : EvmYul.SharedState .Yul) with
          toMachineState :=
            ({ shared with toState := (shared.sload (EvmYul.UInt256.ofNat 0)).1 }
              : EvmYul.SharedState .Yul).toMachineState.mstore
              (EvmYul.UInt256.ofNat 0) (shared.sload (EvmYul.UInt256.ofNat 0)).2 })
      store codeOverride 0 32
  have hF : (fuel + 1) + 7 = fuel + 8 := by omega
  rw [hF] at hSeam
  simpa [simpleStorageLoweredRetrieveCaseBodyTail3, EvmYul.State.sload] using hSeam

/-- Closed-form native exec of the generated scalar-return payload
    `mstore(0, value); return(0, 32)` when the returned word is a literal. -/
private theorem exec_block_loweredLiteralReturnCaseBodyTail_closed
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (value : Nat) :
    EvmYul.Yul.exec (fuel + 8)
        (.Block (loweredLiteralReturnCaseBodyTail value))
        codeOverride (.Ok shared store) =
      let shared1 : EvmYul.SharedState .Yul :=
        { shared with
          toMachineState :=
            shared.toMachineState.mstore
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat value) }
      let shared2 : EvmYul.SharedState .Yul :=
        { shared1 with
          toMachineState :=
            shared1.toMachineState.evmReturn
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
      .error (EvmYul.Yul.Exception.YulHalt (.Ok shared2 store) ⟨1⟩) := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 7))
    (.Block ((loweredLiteralReturnCaseBodyTail value).head! ::
      [(loweredLiteralReturnCaseBodyTail value).getLast!]))
    codeOverride (.Ok shared store) = _
  refine Backends.Native.exec_block_cons_tail_error (fuel + 7) _ _ codeOverride
    (.Ok shared store) _ _
    (by
      have hHead :=
        Backends.Native.exec_lowerExprNative_mstore_lit_lit_ok_fuel
          (fuel + 1) shared store codeOverride 0 value
      simpa [loweredLiteralReturnCaseBodyTail, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hHead) ?_
  have hSeam :=
    Backends.Native.exec_block_singleton_lowerExprNative_return_lit_lit_error_fuel
      fuel
      ({ shared with
          toMachineState :=
          shared.toMachineState.mstore
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat value) })
      store codeOverride 0 32
  simpa [loweredLiteralReturnCaseBodyTail] using hSeam

/-- Closed-form native exec of the generated zero-parameter scalar-return body.
    The body includes `genParamLoads []`'s leading calldata-size guard before
    the literal-return payload. -/
private theorem exec_block_loweredZeroParamLiteralReturnCaseBody_closed
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (value : Nat)
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 4 ≤ shared.executionEnv.calldata.size) :
    EvmYul.Yul.exec (fuel + 10)
        (.Block (loweredZeroParamLiteralReturnCaseBody value))
        codeOverride (.Ok shared store) =
      let shared1 : EvmYul.SharedState .Yul :=
        { shared with
          toMachineState :=
            shared.toMachineState.mstore
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat value) }
      let shared2 : EvmYul.SharedState .Yul :=
        { shared1 with
          toMachineState :=
            shared1.toMachineState.evmReturn
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
      .error (EvmYul.Yul.Exception.YulHalt (.Ok shared2 store) ⟨1⟩) := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 9))
    (.Block ((loweredZeroParamLiteralReturnCaseBody value).head! ::
      loweredLiteralReturnCaseBodyTail value))
    codeOverride (.Ok shared store) = _
  refine Backends.Native.exec_block_cons_tail_error (fuel + 9) _
    (loweredLiteralReturnCaseBodyTail value) codeOverride
    (.Ok shared store) (.Ok shared store) _ ?_ ?_
  · show EvmYul.Yul.exec (fuel + 9)
      (.If (Backends.lowerExprNative
            (.call "lt" [.call "calldatasize" [], .lit 4]))
        [.ExprStmtCall (Backends.lowerExprNative
          (.call "revert" [.lit 0, .lit 0]))])
      codeOverride (.Ok shared store) = .ok (.Ok shared store)
    exact Backends.Native.exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel
      fuel _ codeOverride shared store 4 hSize (by decide) hGe
  · have hTail :=
      exec_block_loweredLiteralReturnCaseBodyTail_closed
        (fuel + 1) codeOverride shared store value
    rw [show fuel + 1 + 8 = fuel + 9 by omega] at hTail
    exact hTail

/-- Closed-form native exec of the generated zero-parameter storage-return body.
    The body includes `genParamLoads []`'s leading calldata-size guard before
    the `mstore(0, sload(0)); return(0, 32)` payload. -/
private theorem exec_block_loweredZeroParamSload0ReturnCaseBody_closed
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 4 ≤ shared.executionEnv.calldata.size) :
    EvmYul.Yul.exec (fuel + 10)
        (.Block loweredZeroParamSload0ReturnCaseBody)
        codeOverride (.Ok shared store) =
      let (state', value) := shared.sload (EvmYul.UInt256.ofNat 0)
      let shared1 : EvmYul.SharedState .Yul := { shared with toState := state' }
      let shared2 : EvmYul.SharedState .Yul :=
        { shared1 with
          toMachineState :=
            shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
      let shared3 : EvmYul.SharedState .Yul :=
        { shared2 with
          toMachineState :=
            shared2.toMachineState.evmReturn
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
      .error (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store) ⟨1⟩) := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 9))
    (.Block ((loweredZeroParamSload0ReturnCaseBody).head! ::
      simpleStorageLoweredRetrieveCaseBodyTail3))
    codeOverride (.Ok shared store) = _
  refine Backends.Native.exec_block_cons_tail_error (fuel + 9) _
    simpleStorageLoweredRetrieveCaseBodyTail3 codeOverride
    (.Ok shared store) (.Ok shared store) _ ?_ ?_
  · show EvmYul.Yul.exec (fuel + 9)
      (.If (Backends.lowerExprNative
            (.call "lt" [.call "calldatasize" [], .lit 4]))
        [.ExprStmtCall (Backends.lowerExprNative
          (.call "revert" [.lit 0, .lit 0]))])
      codeOverride (.Ok shared store) = .ok (.Ok shared store)
    exact Backends.Native.exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel
      fuel _ codeOverride shared store 4 hSize (by decide) hGe
  · have hTail :=
      exec_block_simpleStorageLoweredRetrieveCaseBodyTail3_closed
        fuel codeOverride shared store
    simpa [EvmYul.State.sload] using hTail

/-- Closed-form native exec of the generated single-argument scalar-return
    payload `mstore(0, calldataload(4)); return(0, 32)`. -/
private theorem exec_block_loweredCalldataload4ReturnCaseBodyTail_closed
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (hWord : shared.calldataload (EvmYul.UInt256.ofNat 4) =
      Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg) :
    EvmYul.Yul.exec (fuel + 9)
        (.Block loweredCalldataload4ReturnCaseBodyTail)
        codeOverride (.Ok shared store) =
      let value := Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg
      let shared1 : EvmYul.SharedState .Yul :=
        { shared with
          toMachineState :=
            shared.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
      let shared2 : EvmYul.SharedState .Yul :=
        { shared1 with
          toMachineState :=
            shared1.toMachineState.evmReturn
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
      .error (EvmYul.Yul.Exception.YulHalt (.Ok shared2 store) ⟨1⟩) := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 8))
    (.Block ((loweredCalldataload4ReturnCaseBodyTail).head! ::
      [(loweredCalldataload4ReturnCaseBodyTail).getLast!]))
    codeOverride (.Ok shared store) = _
  refine Backends.Native.exec_block_cons_tail_error (fuel + 8) _ _ codeOverride
    (.Ok shared store) _ _
    (by
      have hHead :=
        Backends.Native.exec_lowerExprNative_mstore_lit_calldataload_lit_ok_fuel
          fuel shared store codeOverride 0 4
      simpa [loweredCalldataload4ReturnCaseBodyTail, hWord] using hHead) ?_
  have hSeam :=
    Backends.Native.exec_block_singleton_lowerExprNative_return_lit_lit_error_fuel
      (fuel + 1)
      ({ shared with
          toMachineState :=
            shared.toMachineState.mstore (EvmYul.UInt256.ofNat 0)
              (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg) })
      store codeOverride 0 32
  have hF : (fuel + 1) + 7 = fuel + 8 := by omega
  rw [hF] at hSeam
  simpa [loweredCalldataload4ReturnCaseBodyTail] using hSeam

/-- Closed-form native exec of the generated aligned-argument scalar-return
    payload `mstore(0, calldataload(4 + 32*idx)); return(0, 32)`. -/
private theorem exec_block_loweredCalldataloadReturnCaseBodyTail_closed
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (idx arg : Nat)
    (hWord : shared.calldataload (EvmYul.UInt256.ofNat (4 + 32 * idx)) =
      Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg) :
    EvmYul.Yul.exec (fuel + 9)
        (.Block (loweredCalldataloadReturnCaseBodyTail idx))
        codeOverride (.Ok shared store) =
      let value := Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg
      let shared1 : EvmYul.SharedState .Yul :=
        { shared with
          toMachineState :=
            shared.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
      let shared2 : EvmYul.SharedState .Yul :=
        { shared1 with
          toMachineState :=
            shared1.toMachineState.evmReturn
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
      .error (EvmYul.Yul.Exception.YulHalt (.Ok shared2 store) ⟨1⟩) := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 8))
    (.Block ((loweredCalldataloadReturnCaseBodyTail idx).head! ::
      [(loweredCalldataloadReturnCaseBodyTail idx).getLast!]))
    codeOverride (.Ok shared store) = _
  refine Backends.Native.exec_block_cons_tail_error (fuel + 8) _ _ codeOverride
    (.Ok shared store) _ _
    (by
      have hHead :=
        Backends.Native.exec_lowerExprNative_mstore_lit_calldataload_lit_ok_fuel
          fuel shared store codeOverride 0 (4 + 32 * idx)
      simpa [loweredCalldataloadReturnCaseBodyTail, hWord] using hHead) ?_
  have hSeam :=
    Backends.Native.exec_block_singleton_lowerExprNative_return_lit_lit_error_fuel
      (fuel + 1)
      ({ shared with
          toMachineState :=
            shared.toMachineState.mstore (EvmYul.UInt256.ofNat 0)
              (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg) })
      store codeOverride 0 32
  have hF : (fuel + 1) + 7 = fuel + 8 := by omega
  rw [hF] at hSeam
  simpa [loweredCalldataloadReturnCaseBodyTail] using hSeam

/-- Composed body-level closed form for the SimpleStorage retrieve hit-case.
Stacks the three guard-strip lemmas (head no-op, callvalue, lt-calldatasize)
on top of `_Tail3_closed` to characterize the full lowered retrieve body's
exec output as the closed-form halt error produced by
`mstore(0, sload(0)); return(0, 32)`. The `shared3` form mirrors `_Tail3_closed`. -/
private theorem exec_block_simpleStorageLoweredRetrieveCaseBody_halt
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hWei : shared.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal))
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 4 ≤ shared.executionEnv.calldata.size) :
    EvmYul.Yul.exec (fuel + 12) (.Block simpleStorageLoweredRetrieveCaseBody)
        codeOverride (.Ok shared store) =
      let (state', value) := shared.sload (EvmYul.UInt256.ofNat 0)
      let shared1 : EvmYul.SharedState .Yul := { shared with toState := state' }
      let shared2 : EvmYul.SharedState .Yul :=
        { shared1 with
          toMachineState :=
            shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
      let shared3 : EvmYul.SharedState .Yul :=
        { shared2 with
          toMachineState :=
            shared2.toMachineState.evmReturn
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
      .error (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store) ⟨1⟩) := by
  have hTail3 := exec_block_simpleStorageLoweredRetrieveCaseBodyTail3_closed
    fuel codeOverride shared store
  have hTail2 := exec_block_simpleStorageLoweredRetrieveCaseBodyTail2_lt_strip_error
    fuel codeOverride shared store _ hSize hGe hTail3
  have hTail := exec_block_simpleStorageLoweredRetrieveCaseBodyTail_callvalue_strip_error
    (fuel + 4) codeOverride shared store _ hWei hTail2
  exact exec_block_simpleStorageLoweredRetrieveCaseBody_head_strip_error
    (fuel + 10) codeOverride (.Ok shared store) _ hTail

/-- Concrete characterization of the lowered SimpleStorage source switch
cases. Both bodies are straight-line, so the lowering is deterministic and
the threaded `nextSwitchId` returns unchanged. Strengthens `_lowered_shape`
from a two-element shape with unspecified bodies to a fixed shape with
explicit lowered bodies, anchoring downstream hit-case proofs against the
harness primitive-call lemmas. -/
private theorem simpleStorageBuildSwitchSourceCases_lowered_concrete
    (reservedNames : List String) (nextSwitchId : Nat) :
    Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId
        simpleStorageBuildSwitchSourceCases =
      .ok ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
            (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)],
        nextSwitchId) := by
  simp only [simpleStorageLoweredStoreCaseBody,
    simpleStorageLoweredRetrieveCaseBody,
    simpleStorageBuildSwitchSourceCases, simpleStorageIRContract,
    Compiler.CodegenCommon.dispatchBody,
    Compiler.CodegenCommon.callvalueGuard,
    Compiler.CodegenCommon.calldatasizeGuard,
    List.map_cons, List.map_nil, List.append_nil,
    List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    if_false, Bool.false_eq_true,
    Backends.lowerSwitchCasesNativeWithSwitchIds_cons,
    Backends.lowerSwitchCasesNativeWithSwitchIds_nil,
    Backends.lowerStmtsNativeWithSwitchIds_cons,
    Backends.lowerStmtsNativeWithSwitchIds_nil,
    Backends.lowerStmtGroupNativeWithSwitchIds_comment,
    Backends.lowerStmtGroupNativeWithSwitchIds_let,
    Backends.lowerStmtGroupNativeWithSwitchIds_expr,
    Backends.lowerStmtGroupNativeWithSwitchIds_if,
    Bind.bind, Except.bind, pure, Except.pure]

/-- Closed-form selector-miss bridge endpoint for SimpleStorage native
dispatcher. Takes only source-level selector facts (`selector ≠ 0x6057361d`
and `selector ≠ 0x2e64cec1`, the two SimpleStorage IR selectors) and
produces the dispatcher exec result `.error Revert` at fuel `fuel + 22`
(`= fuel + cases'.length + 20` with `cases'.length = 2`). The proof opens the
`_sourceLowered` existential, derives `cases'.find? = none` and `tags-range`
from the source-cases facts via `_find?_none` / `_tags_eq` chained with
`simpleStorageBuildSwitchSourceCases_find?_none` and `_tags_lt_uint256_size`,
then composes through `_selectorMiss_revert_via_reduction`. This lifts the
remaining selector-miss obligation in the SimpleStorage native dispatcher
bridge to a purely source-level statement. -/
private theorem simpleStorageNativeContract_dispatcherExec_selectorMiss_revert
    (fuel selector : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hSelMissStore : selector ≠ 0x6057361d)
    (hSelMissRetrieve : selector ≠ 0x2e64cec1)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 22)
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (fuel + 7) tx storage observableSlots hNoWrap
  have hLen : cases'.length = 2 := by
    have h := Backends.lowerSwitchCasesNativeWithSwitchIds_length_eq
      _ _ _ _ _ hLowerCases
    rw [h]; rfl
  have hFind : cases'.find? (fun entry => entry.1 == selector) = none :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_find?_none
      _ _ _ _ _ _ hLowerCases
      (simpleStorageBuildSwitchSourceCases_find?_none hSelMissStore hSelMissRetrieve)
  have hTags := Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq
    _ _ _ _ _ hLowerCases
  have hTagsRange : ∀ tag body, (tag, body) ∈ cases' →
      tag < EvmYul.UInt256.size := by
    intro tag body hMem
    have hMemTag : tag ∈ cases'.map (·.1) := List.mem_map_of_mem hMem
    rw [hTags, simpleStorageBuildSwitchSourceCases_map_fst] at hMemTag
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMemTag
    rcases hMemTag with rfl | rfl <;> decide
  have hReduction := hExec
  rw [show (fuel + 7 + 15 : Nat) = fuel + cases'.length + 20 by rw [hLen],
      show (fuel + 7 + 8 : Nat) = fuel + cases'.length + 13 by rw [hLen]]
    at hReduction
  have h := simpleStorageNativeContract_dispatcherExec_selectorMiss_revert_via_reduction
    fuel selector (Backends.freshNativeSwitchId reservedNames n0) cases'
    tx storage observableSlots hSelector hSelectorRange hFind hTagsRange
    hReduction
  rw [show fuel + cases'.length + 20 = fuel + 22 by rw [hLen]] at h
  exact h

/-- Post-`__has_selector := 1` switch-prefix state at a hit, with the matched
flag set: the input state shape consumed by the selected body inside the
lowered native switch's hit branch. -/
private def simpleStorageDispatcherHitBodyInputState
    (switchId : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) : EvmYul.Yul.State :=
  ((((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots ∅).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1)).insert
          (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1)

/-- Hit-case dual of `_selectorMiss_revert_via_reduction` for the
SimpleStorage `store(uint256)` selector: composes the harness-level
`exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error`
with the strengthened-reduction equation, parametric in `cases'`, the lowered
bodies, and the body-execution `err`. -/
private theorem simpleStorageNativeContract_dispatcherExec_storeHit_error_via_reduction
    (fuel switchId : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector :
      0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hCases : cases' = [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')])
    (hBody : ∀ pre suffix, cases' = pre ++ (0x6057361d, storeBody') :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block storeBody')
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) = .error err)
    (hReduction :
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (fuel + cases'.length + 20)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block [Backends.lowerNativeSwitchBlock
            (Yul.YulExpr.call "shr" [Yul.YulExpr.lit Compiler.Constants.selectorShift,
              Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
            switchId cases' [Backends.Native.nativeRevertZeroZeroStmt]])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots ∅).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1))) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + cases'.length + 20)
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) = .error err := by
  rw [hReduction]
  refine (Backends.Native.exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_error_projectResult_eq
    fuel 0x6057361d switchId 0x6057361d cases'
    [Backends.Native.nativeRevertZeroZeroStmt] storeBody'
    Compiler.SimpleStorageNativeWitness.nativeContract
    tx storage [] observableSlots err
    (Backends.Native.projectResult tx storage [] (.error err))
    hSelector ?_ ?_ ?_ ?_ rfl).1
  · rw [hCases]; rfl
  · norm_num [EvmYul.UInt256.size]
  · intro tag body hMem; rw [hCases] at hMem
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hMem
    rcases hMem with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  · convert hBody using 1 <;> rfl

private def simpleStorageLoweredHitCasesShape
    (reservedNames : List String) (n0 midN : Nat)
    (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt) : Prop :=
  Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1)
      simpleStorageBuildSwitchSourceCases =
    .ok ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')], midN)

private theorem simpleStorageNativeContract_dispatcherExec_storeHit_error
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : ∀ (reservedNames : List String) (n0 midN : Nat)
              (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt),
        simpleStorageLoweredHitCasesShape reservedNames n0 midN storeBody' retrieveBody' →
        EvmYul.Yul.exec (fuel + 9) (.Block storeBody')
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0) tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 22) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage observableSlots) =
      .error err := by
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (fuel + 7) tx storage observableSlots hNoWrap
  obtain ⟨storeBody', retrieveBody', hCases⟩ :=
    simpleStorageBuildSwitchSourceCases_lowered_shape reservedNames _ midN cases' hLowerCases
  subst hCases
  have hBody' := hBody reservedNames n0 midN storeBody' retrieveBody' hLowerCases
  have hReduction := hExec
  rw [show (fuel + 7 + 15 : Nat) = fuel + 2 + 20 from by omega,
      show (fuel + 7 + 8 : Nat) = fuel + 2 + 13 from by omega,
      show (2 : Nat) = ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length from rfl] at hReduction
  have h := simpleStorageNativeContract_dispatcherExec_storeHit_error_via_reduction
    fuel (Backends.freshNativeSwitchId reservedNames n0)
    [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')]
    storeBody' retrieveBody' tx storage observableSlots err
    hSelector rfl ?_ hReduction
  · rw [show fuel + ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length + 20 = fuel + 22 from rfl] at h
    exact h
  · rintro (_ | ⟨⟨_, _⟩, rest⟩) suffix hDecomp
    · simp only [List.nil_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hSuf⟩ := hDecomp; subst hSuf; simpa using hBody'
    · exfalso
      simp only [List.cons_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hRest⟩ := hDecomp
      cases rest with
      | nil => simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hRest
               exact absurd hRest.1.1 (by decide)
      | cons _ _ => simp at hRest

private theorem simpleStorageLoweredHitCasesShape_concrete
    {reservedNames : List String} {n0 midN : Nat}
    {storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt}
    (hShape : simpleStorageLoweredHitCasesShape reservedNames n0 midN
      storeBody' retrieveBody') :
    storeBody' = simpleStorageLoweredStoreCaseBody ∧
      retrieveBody' = simpleStorageLoweredRetrieveCaseBody := by
  have hC := simpleStorageBuildSwitchSourceCases_lowered_concrete
    reservedNames (Backends.freshNativeSwitchId reservedNames n0 + 1)
  unfold simpleStorageLoweredHitCasesShape at hShape
  rw [hC] at hShape
  simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq] at hShape
  exact ⟨hShape.1.1.2.symm, hShape.1.2.1.2.symm⟩

/-- Concrete-body variant of `_dispatcherExec_storeHit_error`. The caller now
only has to discharge the body-exec obligation on the *fixed* lowered body
`simpleStorageLoweredStoreCaseBody`, instead of universally over any
`storeBody'` that might come out of the lowering. Uses
`simpleStorageLoweredHitCasesShape_concrete` to specialize the underlying
parametric premise. This strictly weakens the hit-case obligation that the
dispatcher bridge proof has to supply. -/
private theorem simpleStorageNativeContract_dispatcherExec_storeHit_error_concrete
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 9) (.Block simpleStorageLoweredStoreCaseBody)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 22) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_storeHit_error
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0 _ storeBody' _ hShape
  obtain ⟨hStore, _⟩ := simpleStorageLoweredHitCasesShape_concrete hShape
  rw [hStore]
  exact hBody reservedNames n0

private theorem simpleStorageNativeContract_dispatcherExec_storeHit_error_concrete_tail
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hTail : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 8) (.Block simpleStorageLoweredStoreCaseBodyTail)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 22) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_storeHit_error_concrete
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0
  exact exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error
    (fuel + 7) _ _ err (hTail reservedNames n0)

/-- Callvalue-stripped version of `_storeHit_error_concrete_tail`: when the
transaction has zero `msgValue`, the leading `if callvalue() { revert }` guard
is a no-op, so the body-execution premise can be expressed against the
4-statement `simpleStorageLoweredStoreCaseBodyTail2` at fuel `+7` instead of
the 5-statement `simpleStorageLoweredStoreCaseBodyTail` at fuel `+8`. Strictly
shrinks the dispatcher hit-case body-exec obligation under the natural Solidity
assumption that non-payable functions are called with `msg.value = 0`. -/
private theorem simpleStorageNativeContract_dispatcherExec_storeHit_error_concrete_tail2
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue = 0)
    (hTail2 : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 7)
          (.Block simpleStorageLoweredStoreCaseBodyTail2)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 22) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_storeHit_error_concrete_tail
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0
  have hWei :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.weiValue =
      (⟨0⟩ : EvmYul.Literal) := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_weiValue,
        hMsgValue]
    rfl
  have hT2 := hTail2 reservedNames n0
  show EvmYul.Yul.exec (fuel + 8) (.Block simpleStorageLoweredStoreCaseBodyTail)
    (some Compiler.SimpleStorageNativeWitness.nativeContract)
    (.Ok _ _) = .error err
  exact exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error
    fuel _ _ _ err hWei hT2

private theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_via_reduction
    (fuel switchId : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector :
      0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hCases : cases' = [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')])
    (hBody : ∀ pre suffix, cases' = pre ++ (0x2e64cec1, retrieveBody') :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block retrieveBody')
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) = .error err)
    (hReduction :
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (fuel + cases'.length + 20)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block [Backends.lowerNativeSwitchBlock
            (Yul.YulExpr.call "shr" [Yul.YulExpr.lit Compiler.Constants.selectorShift,
              Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
            switchId cases' [Backends.Native.nativeRevertZeroZeroStmt]])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots ∅).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1))) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + cases'.length + 20)
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) = .error err := by
  rw [hReduction]
  refine (Backends.Native.exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_error_projectResult_eq
    fuel 0x2e64cec1 switchId 0x2e64cec1 cases'
    [Backends.Native.nativeRevertZeroZeroStmt] retrieveBody'
    Compiler.SimpleStorageNativeWitness.nativeContract
    tx storage [] observableSlots err
    (Backends.Native.projectResult tx storage [] (.error err))
    hSelector ?_ ?_ ?_ ?_ rfl).1
  · rw [hCases]; rfl
  · norm_num [EvmYul.UInt256.size]
  · intro tag body hMem; rw [hCases] at hMem
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hMem
    rcases hMem with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  · convert hBody using 1 <;> rfl

private theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : ∀ (reservedNames : List String) (n0 midN : Nat)
              (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt),
        simpleStorageLoweredHitCasesShape reservedNames n0 midN storeBody' retrieveBody' →
        EvmYul.Yul.exec (fuel + 8) (.Block retrieveBody')
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0) tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 22) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage observableSlots) =
      .error err := by
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (fuel + 7) tx storage observableSlots hNoWrap
  obtain ⟨storeBody', retrieveBody', hCases⟩ :=
    simpleStorageBuildSwitchSourceCases_lowered_shape reservedNames _ midN cases' hLowerCases
  subst hCases
  have hBody' := hBody reservedNames n0 midN storeBody' retrieveBody' hLowerCases
  have hReduction := hExec
  rw [show (fuel + 7 + 15 : Nat) = fuel + 2 + 20 from by omega,
      show (fuel + 7 + 8 : Nat) = fuel + 2 + 13 from by omega,
      show (2 : Nat) = ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length from rfl] at hReduction
  have h := simpleStorageNativeContract_dispatcherExec_retrieveHit_error_via_reduction
    fuel (Backends.freshNativeSwitchId reservedNames n0)
    [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')]
    storeBody' retrieveBody' tx storage observableSlots err
    hSelector rfl ?_ hReduction
  · rw [show fuel + ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length + 20 = fuel + 22 from rfl] at h
    exact h
  · rintro (_ | ⟨⟨_, _⟩, rest⟩) suffix hDecomp
    · exfalso
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hDecomp
      exact absurd hDecomp.1.1 (by decide)
    · simp only [List.cons_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hRest⟩ := hDecomp
      cases rest with
      | nil => simp only [List.nil_append, List.cons.injEq] at hRest
               obtain ⟨_, hSuf⟩ := hRest; subst hSuf; simpa using hBody'
      | cons _ _ => simp at hRest

private theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 8) (.Block simpleStorageLoweredRetrieveCaseBody)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 22) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_retrieveHit_error
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0 _ _ retrieveBody' hShape
  obtain ⟨_, hRetrieve⟩ := simpleStorageLoweredHitCasesShape_concrete hShape
  rw [hRetrieve]
  exact hBody reservedNames n0

private theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete_tail
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hTail : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 7) (.Block simpleStorageLoweredRetrieveCaseBodyTail)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 22) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0
  exact exec_block_simpleStorageLoweredRetrieveCaseBody_head_strip_error
    (fuel + 6) _ _ err (hTail reservedNames n0)

/-- Retrieve-case dual of `_storeHit_error_concrete_tail2`. -/
private theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete_tail2
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0)
    (hTail2 : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 6)
          (.Block simpleStorageLoweredRetrieveCaseBodyTail2)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 22) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete_tail
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0
  have hWei :
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).executionEnv.weiValue =
      (⟨0⟩ : EvmYul.Literal) := by
    rw [nativeSwitchPostInitFreeMemorySharedState_weiValue]
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    simpa [Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256,
      EvmYul.UInt256.ofNat, Fin.ofNat] using hMsgValue
  have hT2 := hTail2 reservedNames n0
  show EvmYul.Yul.exec (fuel + 7) (.Block simpleStorageLoweredRetrieveCaseBodyTail)
    (some Compiler.SimpleStorageNativeWitness.nativeContract)
    (.Ok _ _) = .error err
  exact exec_block_simpleStorageLoweredRetrieveCaseBodyTail_callvalue_strip_error
    fuel _ _ _ err hWei hT2

/-- Retrieve-case wrapper that further shrinks the body-exec obligation by
also stripping the inner `if lt(calldatasize(), 4) {…}` argument-length revert
guard. The user supplies the tail3 obligation (the 2-statement
`mstore(0, sload(0)); return(0, 32)` core) and the wrapper discharges both
the callvalue and lt-calldatasize guards via the strip lemmas. The
calldata-size assumptions are derived automatically from `hNoWrap` and
`initialState_calldataSize`. -/
private theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete_tail3
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0)
    (hTail3 : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 9)
          (.Block simpleStorageLoweredRetrieveCaseBodyTail3)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 26) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete_tail2
    (fuel + 4) tx storage observableSlots err hSelector hNoWrap hMsgValue ?_
  intro reservedNames n0
  have hT3 := hTail3 reservedNames n0
  have hSize :
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).executionEnv.calldata.size <
      EvmYul.UInt256.size := by
    rw [nativeSwitchPostInitFreeMemorySharedState_calldata_size]
    exact hNoWrap
  have hGe :
      4 ≤ (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).executionEnv.calldata.size := by
    rw [nativeSwitchPostInitFreeMemorySharedState_calldata_size]
    exact Nat.le_add_right 4 _
  show EvmYul.Yul.exec ((fuel + 4) + 6)
    (.Block simpleStorageLoweredRetrieveCaseBodyTail2)
    (some Compiler.SimpleStorageNativeWitness.nativeContract)
    (.Ok _ _) = .error err
  exact exec_block_simpleStorageLoweredRetrieveCaseBodyTail2_lt_strip_error
    fuel _ _ _ err hSize hGe hT3

private noncomputable def simpleStorageNativeDispatcherFuel : Nat :=
  sizeOf [Compiler.CodegenCommon.initFreeMemoryPointer,
    Compiler.CodegenCommon.buildSwitch simpleStorageIRContract.functions none none]

/-- Lower bound on the SimpleStorage native dispatcher fuel constant for
the retrieve-hit and store-hit bridges, which use the `_concrete_tail3`
chain that produces dispatcher exec at `fuel + 26`. -/
private theorem simpleStorageNativeDispatcherFuel_ge_26 :
    simpleStorageNativeDispatcherFuel ≥ 26 := by
  unfold simpleStorageNativeDispatcherFuel
  decide

private theorem simpleStorageNativeDispatcherFuel_ge_22 :
    simpleStorageNativeDispatcherFuel ≥ 22 := by
  exact Nat.le_trans (by decide) simpleStorageNativeDispatcherFuel_ge_26

/-- Native dispatcher exec at exactly `simpleStorageNativeDispatcherFuel`
reduces to `.error Revert` for the selector-miss class. -/
private theorem simpleStorageNativeContract_dispatcherExec_selectorMiss_revert_atFuel
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelectorRange : tx.functionSelector % Compiler.Constants.selectorModulus
        < EvmYul.UInt256.size)
    (hSelMissStore : tx.functionSelector % Compiler.Constants.selectorModulus
        ≠ 0x6057361d)
    (hSelMissRetrieve : tx.functionSelector % Compiler.Constants.selectorModulus
        ≠ 0x2e64cec1)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        simpleStorageNativeDispatcherFuel
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  have hReshape : simpleStorageNativeDispatcherFuel =
      (simpleStorageNativeDispatcherFuel - 22) + 22 :=
    (Nat.sub_add_cancel simpleStorageNativeDispatcherFuel_ge_22).symm
  rw [hReshape]
  exact simpleStorageNativeContract_dispatcherExec_selectorMiss_revert
    (simpleStorageNativeDispatcherFuel - 22)
    (tx.functionSelector % Compiler.Constants.selectorModulus)
    tx storage observableSlots
    rfl hSelectorRange hSelMissStore hSelMissRetrieve hNoWrap

/-- Closed-form `interpretIR` reduction for the SimpleStorage selector-miss
class. Given the two raw selector mismatches (`≠ 0x6057361d` and
`≠ 0x2e64cec1`), `interpretIR` falls into the `find?`-`none` branch and returns
the trivial reverted shape with storage and events untouched. -/
private theorem interpretIR_simpleStorage_selectorMiss
    (tx : IRTransaction) (initialState : IRState)
    (hSelMissStore : tx.functionSelector ≠ 0x6057361d)
    (hSelMissRetrieve : tx.functionSelector ≠ 0x2e64cec1) :
    interpretIR simpleStorageIRContract tx initialState =
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events } := by
  unfold interpretIR
  simp only [simpleStorageIRContract, List.find?]
  have hstore : (0x6057361d == tx.functionSelector) = false := by
    simp [BEq.beq, hSelMissStore.symm]
  have hretrieve : (0x2e64cec1 == tx.functionSelector) = false := by
    simp [BEq.beq, hSelMissRetrieve.symm]
  simp [hstore, hretrieve]

/-- Closed-form `interpretIR` reduction for the SimpleStorage retrieve-hit
class. Given the raw selector match (`= 0x2e64cec1`), `interpretIR` enters the
`retrieve` body which is read-only on storage: it loads slot 0 via `sload`,
mirrors it into memory[0..32] via `mstore`, and returns those 32 bytes. The
returned word equals `(state.storage (IRStorageSlot.ofNat 0)).toNat` (where `state` is
`initialState.withTx tx`). Storage and events are unchanged.

  After Phase 1 of the IR storage refactor,
  `state.storage (IRStorageSlot.ofNat 0) : IRStorageWord` is `UInt256`-bounded,
  so `(state.storage (IRStorageSlot.ofNat 0)).toNat < 2^256`. This is the
IR-side input to the direct native retrieve-hit match proof. -/
private theorem interpretIR_simpleStorage_retrieveHit
    (tx : IRTransaction) (initialState : IRState)
    (hSel : tx.functionSelector = 0x2e64cec1)
    (hMsgValue : tx.msgValue % evmModulus = 0) :
      interpretIR simpleStorageIRContract tx initialState =
        { success := true
          returnValue := some ((initialState.storage (IRStorageSlot.ofNat 0)).toNat)
          finalStorage := initialState.storage
          finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
          events := initialState.events } := by
  have hstore : (0x6057361d == tx.functionSelector) = false := by
    simp [BEq.beq, hSel]
  have hretrieve : (0x2e64cec1 == tx.functionSelector) = true := by
    simp [BEq.beq, hSel]
  -- Closed-form evaluation of the retrieve body for any fuel ≥ 2.
  have hbody : ∀ (n : Nat) (s : IRState), 2 ≤ n →
      execIRStmts (n + 1) s
        [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
         Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] =
          .return ((s.storage (IRStorageSlot.ofNat 0)).toNat)
            { s with memory := fun o =>
                if o = 0 then (s.storage (IRStorageSlot.ofNat 0)).toNat else s.memory o } := by
    intro n s hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    -- Fuel `k + 2 + 1 = k + 3` is `Nat.succ (Nat.succ (Nat.succ k))`, allowing
    -- both the outer `execIRStmts` and the inner `execIRStmt` to step.
    simp +decide only [execIRStmts, execIRStmt, evalIRExpr, evalIRCall_sload_singleton,
      Compiler.Proofs.abstractLoadStorageOrMapping,
      Option.bind_some, ↓reduceIte]
  -- The retrieve body has at least 2 statements, so `sizeOf body ≥ 2` by
  -- direct computation on the auto-derived size measure.
  have hsize : 2 ≤ sizeOf
      ([Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
        Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] : List Yul.YulStmt) := by
    decide
  unfold interpretIR
  simp only [simpleStorageIRContract, List.find?, hstore, hretrieve,
    List.length_nil, Nat.zero_le, ↓reduceDIte]
  -- Now goal involves `execIRFunction retrieveFn tx.args state'`.
  unfold execIRFunction
  simp only [List.zip_nil_left, List.foldl_nil]
  -- Goal: `match execIRStmts (sizeOf body + 1) state' body with ... = ...`.
  rw [hbody _ _ hsize]
  simp [hMsgValue]

/-- Closed-form `interpretIR` reduction for the SimpleStorage store-hit class
when the ABI argument is present. The IR setter writes the first calldata word
to bounded storage slot zero and stops successfully. -/
private theorem interpretIR_simpleStorage_storeHit_arg
    (tx : IRTransaction) (initialState : IRState)
    (arg : Nat) (rest : List Nat)
    (hSel : tx.functionSelector = 0x6057361d)
    (hArgs : tx.args = arg :: rest)
    (hMsgValue : tx.msgValue % evmModulus = 0) :
      interpretIR simpleStorageIRContract tx initialState =
        { success := true
          returnValue := none
          finalStorage :=
            Compiler.Proofs.abstractStoreStorageOrMapping initialState.storage 0
              (arg % evmModulus)
          finalMappings :=
            Compiler.Proofs.storageAsMappings
              (Compiler.Proofs.abstractStoreStorageOrMapping initialState.storage 0
                (arg % evmModulus))
          events := initialState.events } := by
  have hstore : (0x6057361d == tx.functionSelector) = true := by
    simp [BEq.beq, hSel]
  let storeFn : IRFunction :=
    { name := "store"
      selector := 0x6057361d
      params := [{ name := "value", ty := IRType.uint256 }]
      ret := IRType.unit
      body := [
        Yul.YulStmt.let_ "value" (Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]),
        Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
          [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
        Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])] }
  have hExec :=
    Compiler.Proofs.IRGeneration.execIRFunction_store0_calldataload4_stop_of_args_cons
      storeFn tx initialState arg rest (by rfl) hArgs
  unfold interpretIR
  simp only [simpleStorageIRContract, List.find?, hstore, List.length_cons,
    List.length_nil, Nat.reduceAdd]
  simpa [storeFn, applyIRTransactionContext, hArgs, hMsgValue, evmModulus] using hExec

/-- Closed-form `interpretIR` reduction for the SimpleStorage store-hit class
when calldata is too short for the single setter argument. The dispatcher
selects the function, but the IR arity guard fails before executing the body. -/
private theorem interpretIR_simpleStorage_storeHit_short
    (tx : IRTransaction) (initialState : IRState)
    (hSel : tx.functionSelector = 0x6057361d)
    (hShort : tx.args = []) :
      interpretIR simpleStorageIRContract tx initialState =
        { success := false
          returnValue := none
          finalStorage := initialState.storage
          finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
          events := initialState.events } := by
  have hstore : (0x6057361d == tx.functionSelector) = true := by
    simp [BEq.beq, hSel]
  unfold interpretIR
  simp [simpleStorageIRContract, hstore, hShort]

/-- Native dispatcher exec at exactly `simpleStorageNativeDispatcherFuel`
reduces to `.error (YulHalt (.Ok shared3 _) ⟨1⟩)` for the retrieve-hit class,
where `shared3` is the closed-form shared state after the
`mstore(0, sload(0))` and `return(0, 32)` updates. The Yul varStore inside
the halt state depends on the fresh switch identifier (which the dispatcher
chose internally), so it is left existentially quantified — `projectResult`
on `.error (YulHalt _ _)` ignores the varStore, so this is sufficient for
the bridge proof. Composes the body-level closed form
`exec_block_simpleStorageLoweredRetrieveCaseBody_halt` with
`_retrieveHit_error_via_reduction` after opening the `_sourceLowered`
existential and pinning `cases'` via `_lowered_shape` and
`_lowered_concrete`. The `_concrete_tail*` chain is bypassed because it
universally quantifies over `(reservedNames, n0)` against a single fixed
`err`, which is incompatible with the switchId-dependent varStore inside
the halt-error term. -/
private theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_halt_atFuel
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) :
    let shared :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage observableSlots
    let p := shared.sload (EvmYul.UInt256.ofNat 0)
    let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
    let shared3 : EvmYul.SharedState .Yul :=
      { shared2 with
        toMachineState :=
          shared2.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    ∃ store : EvmYul.Yul.VarStore,
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          simpleStorageNativeDispatcherFuel
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract tx storage
            observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store) ⟨1⟩) := by
  -- Bring the let-bound names from the goal into the local context.
  intro shared p shared1 shared2 shared3
  -- Reshape dispatcher fuel to `g + 26` where `g := dispatcherFuel - 26`.
  set g := simpleStorageNativeDispatcherFuel - 26 with hg_def
  have hReshape : simpleStorageNativeDispatcherFuel = g + 26 :=
    by simpa [g] using
      (Nat.sub_add_cancel simpleStorageNativeDispatcherFuel_ge_26).symm
  rw [hReshape]
  -- Open the `_sourceLowered` existential at `peeledFuel := g + 11`, so the
  -- dispatcher LHS lands at `(g + 11) + 14 = g + 26`.
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (g + 11) tx storage observableSlots hNoWrap
  -- Pin `cases'` to the two-element shape.
  obtain ⟨storeBody', retrieveBody', hCases⟩ :=
    simpleStorageBuildSwitchSourceCases_lowered_shape reservedNames _ midN
      cases' hLowerCases
  subst hCases
  -- Pin the lowered bodies to the concrete forms.
  obtain ⟨hStoreBody, hRetrieveBody⟩ :=
    simpleStorageLoweredHitCasesShape_concrete hLowerCases
  subst hStoreBody
  subst hRetrieveBody
  -- The chained-insert varStore for the dispatcher hit-body input state.
  set switchId := Backends.freshNativeSwitchId reservedNames n0 with hSw
  let store_body : EvmYul.Yul.VarStore :=
    ((((∅ : EvmYul.Yul.VarStore).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)).insert
          (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1)
  -- Provide `store := store_body` for the existential.
  refine ⟨store_body, ?_⟩
  -- Discharge the body-level closed form via `_RetrieveCaseBody_halt`.
  have hWei :
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).executionEnv.weiValue =
      (⟨0⟩ : EvmYul.Literal) := by
    rw [nativeSwitchPostInitFreeMemorySharedState_weiValue]
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    simpa [Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256,
      EvmYul.UInt256.ofNat, Fin.ofNat] using hMsgValue
  have hSize :
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).executionEnv.calldata.size <
      EvmYul.UInt256.size := by
    rw [nativeSwitchPostInitFreeMemorySharedState_calldata_size]
    exact hNoWrap
  have hGe :
      4 ≤ (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).executionEnv.calldata.size := by
    rw [nativeSwitchPostInitFreeMemorySharedState_calldata_size]
    exact Nat.le_add_right 4 _
  have hBodyHalt :=
    exec_block_simpleStorageLoweredRetrieveCaseBody_halt g
      (some Compiler.SimpleStorageNativeWitness.nativeContract)
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots)
      store_body hWei hSize hGe
  -- Reshape `hExec` into the form expected by `_via_reduction`'s
  -- `hReduction` parameter.
  have hReduction := hExec
  rw [show (g + 11 + 15 : Nat) = (g + 4) + 2 + 20 from by omega,
      show (g + 11 + 8 : Nat) = (g + 4) + 2 + 13 from by omega,
      show (2 : Nat) = ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length from rfl] at hReduction
  -- Body-execution premise of `_via_reduction`: only valid decomposition is
  -- `pre = [(0x6057361d, store)]`, `suffix = []`. Body fuel is
  -- `(g + 4 + 1) + 0 + 7 = g + 12`, matching `hBodyHalt`.
  have hBodyExec : ∀ pre suffix,
      ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)) =
        pre ++ (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody) :: suffix →
      EvmYul.Yul.exec (((g + 4) + 1) + suffix.length + 7)
        (.Block simpleStorageLoweredRetrieveCaseBody)
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store_body) ⟨1⟩) := by
    rintro pre suffix hDecomp
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hDecomp
      exfalso
      exact absurd hDecomp.1.1 (by decide)
    | cons _ rest =>
      simp only [List.cons_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hRest⟩ := hDecomp
      cases rest with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hRest
        obtain ⟨_, hSuf⟩ := hRest
        subst suffix
        simp only [List.length_nil, Nat.add_zero]
        rw [show g + 4 + 1 + 7 = g + 12 by omega]
        exact hBodyHalt
      | cons _ _ => simp at hRest
  -- Apply `_retrieveHit_error_via_reduction` at `fuel := g + 4` with
  -- `err := YulHalt (.Ok shared3 store_body) ⟨1⟩`.
  have h := simpleStorageNativeContract_dispatcherExec_retrieveHit_error_via_reduction
    (g + 4) switchId
    [(0x6057361d, simpleStorageLoweredStoreCaseBody),
     (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)]
    simpleStorageLoweredStoreCaseBody simpleStorageLoweredRetrieveCaseBody
    tx storage observableSlots
    (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store_body) ⟨1⟩)
    hSelector rfl hBodyExec hReduction
  -- `h` has dispatcher fuel `(g + 4) + cases'.length + 19`. Reshape to `g + 26`.
  have hLen :
      ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length = 2 := rfl
  rw [hLen, show (g + 4) + 2 + 20 = g + 26 from by omega] at h
  exact h

/-- Native dispatcher exec at exactly `simpleStorageNativeDispatcherFuel`
reduces to the `STOP` halt for the store-hit class when calldata supplies the
setter argument. -/
private theorem simpleStorageNativeContract_dispatcherExec_storeHit_halt_atFuel
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) :
    ∃ store_body haltState,
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          simpleStorageNativeDispatcherFuel
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract tx storage
            observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState ⟨0⟩) ∧
      haltState =
        let initialWithStore : EvmYul.Yul.State :=
          .Ok (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
            Compiler.SimpleStorageNativeWitness.nativeContract tx storage
            observableSlots) store_body
        let withValue := initialWithStore.insert "value"
          (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
        withValue.setState
          (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
            (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)) := by
  set g := simpleStorageNativeDispatcherFuel - 26 with hg_def
  have hReshape : simpleStorageNativeDispatcherFuel = g + 26 :=
    by simpa [g] using
      (Nat.sub_add_cancel simpleStorageNativeDispatcherFuel_ge_26).symm
  rw [hReshape]
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (g + 11) tx storage observableSlots hNoWrap
  obtain ⟨storeBody', retrieveBody', hCases⟩ :=
    simpleStorageBuildSwitchSourceCases_lowered_shape reservedNames _ midN
      cases' hLowerCases
  subst hCases
  obtain ⟨hStoreBody, hRetrieveBody⟩ :=
    simpleStorageLoweredHitCasesShape_concrete hLowerCases
  subst hStoreBody
  subst hRetrieveBody
  set switchId := Backends.freshNativeSwitchId reservedNames n0 with hSw
  let store_body : EvmYul.Yul.VarStore :=
    ((((∅ : EvmYul.Yul.VarStore).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)).insert
          (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1)
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      Compiler.SimpleStorageNativeWitness.nativeContract tx storage
      observableSlots) store_body
  let withValue := initialWithStore.insert "value"
    (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
  let finalState := withValue.setState
    (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
  refine ⟨store_body, finalState, ?_, ?_⟩
  · have hWei :
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots).executionEnv.weiValue =
        (⟨0⟩ : EvmYul.Literal) := by
      rw [nativeSwitchPostInitFreeMemorySharedState_weiValue]
      apply congrArg EvmYul.UInt256.mk
      apply Fin.ext
      simpa [Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256,
        EvmYul.UInt256.ofNat, Fin.ofNat] using hMsgValue
    have hSize :
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots).executionEnv.calldata.size <
        EvmYul.UInt256.size := by
      rw [nativeSwitchPostInitFreeMemorySharedState_calldata_size]
      exact hNoWrap
    have hGe :
        36 ≤ (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots).executionEnv.calldata.size := by
      rw [nativeSwitchPostInitFreeMemorySharedState_calldata_size]
      rw [hArgs]
      simp
      omega
    have hPerm :
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots).executionEnv.perm = true :=
      nativeSwitchPostInitFreeMemorySharedState_perm
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage observableSlots
    have hWord :
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots).calldataload (EvmYul.UInt256.ofNat 4) =
          Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg := by
      simpa [Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
        Compiler.Proofs.YulGeneration.Backends.Native.initialState,
        EvmYul.Yul.State.sharedState, EvmYul.Yul.State.toState] using
        Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataload4_arg0_word
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage observableSlots
          arg rest hArgs
    have hBodyHalt :=
      exec_block_simpleStorageLoweredStoreCaseBody_halt g
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots)
        tx storage observableSlots store_body arg rest hArgs hPerm hWord hWei hSize hGe
    have hReduction := hExec
    rw [show (g + 11 + 15 : Nat) = (g + 4) + 2 + 20 from by omega,
        show (g + 11 + 8 : Nat) = (g + 4) + 2 + 13 from by omega,
        show (2 : Nat) = ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
          (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
          List (Nat × List EvmYul.Yul.Ast.Stmt)).length from rfl] at hReduction
    have hBodyExec : ∀ pre suffix,
        ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
          (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
          List (Nat × List EvmYul.Yul.Ast.Stmt)) =
          pre ++ (0x6057361d, simpleStorageLoweredStoreCaseBody) :: suffix →
        EvmYul.Yul.exec (((g + 4) + 1) + suffix.length + 7)
          (.Block simpleStorageLoweredStoreCaseBody)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState switchId tx storage
            observableSlots) =
          .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
      rintro pre suffix hDecomp
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hDecomp
        obtain ⟨_, hSuf⟩ := hDecomp
        subst suffix
        simp only [List.length_cons, List.length_nil, Nat.add_zero]
        rw [show g + 4 + 1 + 1 + 7 = g + 13 by omega]
        exact hBodyHalt
      | cons _ restPre =>
        exfalso
        simp only [List.cons_append, List.cons.injEq] at hDecomp
        obtain ⟨_, hRest⟩ := hDecomp
        cases restPre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hRest
          exact absurd hRest.1.1 (by decide)
        | cons _ _ => simp at hRest
    have h := simpleStorageNativeContract_dispatcherExec_storeHit_error_via_reduction
      (g + 4) switchId
      [(0x6057361d, simpleStorageLoweredStoreCaseBody),
       (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)]
      simpleStorageLoweredStoreCaseBody simpleStorageLoweredRetrieveCaseBody
      tx storage observableSlots
      (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩)
      hSelector rfl hBodyExec hReduction
    have hLen :
        ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
          (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
          List (Nat × List EvmYul.Yul.Ast.Stmt)).length = 2 := rfl
    rw [hLen, show (g + 4) + 2 + 20 = g + 26 from by omega] at h
    exact h
  · rfl

/-- Native dispatcher exec at exactly `simpleStorageNativeDispatcherFuel`
reverts for the store-hit class when calldata contains no setter argument. -/
private theorem simpleStorageNativeContract_dispatcherExec_storeHit_short_revert_atFuel
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hArgs : tx.args = [])
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        simpleStorageNativeDispatcherFuel
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  set g := simpleStorageNativeDispatcherFuel - 26 with hg_def
  have hReshape : simpleStorageNativeDispatcherFuel = g + 26 :=
    by simpa [g] using
      (Nat.sub_add_cancel simpleStorageNativeDispatcherFuel_ge_26).symm
  rw [hReshape]
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (g + 11) tx storage observableSlots hNoWrap
  obtain ⟨storeBody', retrieveBody', hCases⟩ :=
    simpleStorageBuildSwitchSourceCases_lowered_shape reservedNames _ midN
      cases' hLowerCases
  subst hCases
  obtain ⟨hStoreBody, hRetrieveBody⟩ :=
    simpleStorageLoweredHitCasesShape_concrete hLowerCases
  subst hStoreBody
  subst hRetrieveBody
  set switchId := Backends.freshNativeSwitchId reservedNames n0 with hSw
  let store_body : EvmYul.Yul.VarStore :=
    ((((∅ : EvmYul.Yul.VarStore).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)).insert
          (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1)
  have hWei :
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).executionEnv.weiValue =
      (⟨0⟩ : EvmYul.Literal) := by
    rw [nativeSwitchPostInitFreeMemorySharedState_weiValue]
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    simpa [Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256,
      EvmYul.UInt256.ofNat, Fin.ofNat] using hMsgValue
  have hSizeEq :
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).executionEnv.calldata.size = 4 := by
    rw [nativeSwitchPostInitFreeMemorySharedState_calldata_size]
    simp [hArgs]
  have hTail2 :=
    exec_block_simpleStorageLoweredStoreCaseBodyTail2_short_revert
      g (some Compiler.SimpleStorageNativeWitness.nativeContract)
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots)
      store_body hSizeEq
  have hTail :=
    exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error
      (g + 4) (some Compiler.SimpleStorageNativeWitness.nativeContract)
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots)
      store_body _ hWei hTail2
  have hBodyRevert :
      EvmYul.Yul.exec (g + 13) (.Block simpleStorageLoweredStoreCaseBody)
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) =
        .error EvmYul.Yul.Exception.Revert := by
    exact exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error
      (g + 11) _ _ _ hTail
  have hReduction := hExec
  rw [show (g + 11 + 15 : Nat) = (g + 4) + 2 + 20 from by omega,
      show (g + 11 + 8 : Nat) = (g + 4) + 2 + 13 from by omega,
      show (2 : Nat) = ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length from rfl] at hReduction
  have hBodyExec : ∀ pre suffix,
      ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)) =
        pre ++ (0x6057361d, simpleStorageLoweredStoreCaseBody) :: suffix →
      EvmYul.Yul.exec (((g + 4) + 1) + suffix.length + 7)
        (.Block simpleStorageLoweredStoreCaseBody)
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) =
        .error EvmYul.Yul.Exception.Revert := by
    rintro pre suffix hDecomp
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hSuf⟩ := hDecomp
      subst hSuf
      simpa [simpleStorageDispatcherHitBodyInputState, store_body] using hBodyRevert
    | cons _ restPre =>
      exfalso
      simp only [List.cons_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hRest⟩ := hDecomp
      cases restPre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hRest
        exact absurd hRest.1.1 (by decide)
      | cons _ _ => simp at hRest
  have h := simpleStorageNativeContract_dispatcherExec_storeHit_error_via_reduction
    (g + 4) switchId
    [(0x6057361d, simpleStorageLoweredStoreCaseBody),
     (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)]
    simpleStorageLoweredStoreCaseBody simpleStorageLoweredRetrieveCaseBody
    tx storage observableSlots EvmYul.Yul.Exception.Revert
    hSelector rfl hBodyExec hReduction
  have hLen :
      ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length = 2 := rfl
  rw [hLen, show (g + 4) + 2 + 20 = g + 26 from by omega] at h
  exact h

/-- Projected native storage after the generated `store(uint256)` body agrees
with the IR setter update on every materialized slot. The native zero-write
case erases slot zero from the finite EVM map; projected lookup still agrees
with IR storage because missing native storage reads as the zero word. -/
private theorem simpleStorage_storage_get?_insert_of_ne
    (m : EvmYul.Storage) (lookup inserted value : EvmYul.UInt256)
    (h : compare lookup inserted ≠ Ordering.eq) :
    (m.insert inserted value)[lookup]? = m[lookup]? := by
  rw [Std.TreeMap.getElem?_insert]
  split
  · rename_i heq
    exact False.elim (h (Std.OrientedCmp.eq_comm.mp heq))
  · rfl

private theorem simpleStorage_storage_get?_insert_of_eq
    (m : EvmYul.Storage) (lookup inserted value : EvmYul.UInt256)
    (h : compare lookup inserted = Ordering.eq) :
    (m.insert inserted value)[lookup]? = some value := by
  rw [Std.TreeMap.getElem?_insert]
  exact if_pos (Std.OrientedCmp.eq_comm.mpr h)

private theorem simpleStorage_storage_get?_erase_of_ne
    (m : EvmYul.Storage) (lookup erased : EvmYul.UInt256)
    (h : compare lookup erased ≠ Ordering.eq) :
    (m.erase erased)[lookup]? = m[lookup]? := by
  rw [Std.TreeMap.getElem?_erase]
  split
  · rename_i heq
    exact False.elim (h (Std.OrientedCmp.eq_comm.mp heq))
  · rfl

private theorem simpleStorage_account_updateStorage_storage_of_nonzero
    {τ : EvmYul.OperationType} (account : EvmYul.Account τ)
    (slot value : EvmYul.UInt256)
    (hValueNonzero : (value == (⟨0⟩ : EvmYul.UInt256)) = false) :
    (account.updateStorage slot value).storage =
      account.storage.insert slot value := by
  unfold EvmYul.Account.updateStorage
  change (value == EvmYul.UInt256.ofNat 0) = false at hValueNonzero
  split
  · rename_i hZero
    change (value == EvmYul.UInt256.ofNat 0) = true at hZero
    rw [hValueNonzero] at hZero
    contradiction
  · rfl

private theorem simpleStorage_account_updateStorage_storage_of_zero
    {τ : EvmYul.OperationType} (account : EvmYul.Account τ)
    (slot value : EvmYul.UInt256)
    (hValueZero : (value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    (account.updateStorage slot value).storage =
      account.storage.erase slot := by
  unfold EvmYul.Account.updateStorage
  change (value == EvmYul.UInt256.ofNat 0) = true at hValueZero
  split
  · rfl
  · rename_i hNonzero
    simp only [Bool.not_eq_true] at hNonzero
    change (value == EvmYul.UInt256.ofNat 0) = false at hNonzero
    rw [hValueZero] at hNonzero
    contradiction

@[simp] private theorem
    nativeSwitchPostInitFreeMemorySharedState_toState
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (slots : List Nat) :
    (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage slots).toState =
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        contract tx storage slots).sharedState.toState := by
  rfl

private theorem projectStorageFromState_eq_of_accountMap_eq
    (tx : YulTransaction) (left right : EvmYul.Yul.State)
    (h :
      left.sharedState.accountMap =
        right.sharedState.accountMap) :
    Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState tx left =
      Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState tx right := by
  unfold Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
  unfold Compiler.Proofs.YulGeneration.Backends.StateBridge.extractStorage
  rw [h]

private theorem projectStorageFromState_insert_sstore_eq_of_toState_eq
    (tx : YulTransaction)
    (leftShared rightShared : EvmYul.SharedState .Yul)
    (leftStore rightStore : EvmYul.Yul.VarStore)
    (name : String) (value slot stored : EvmYul.UInt256)
    (hState : leftShared.toState = rightShared.toState) :
    Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState tx
        (((EvmYul.Yul.State.Ok leftShared leftStore).insert name value).setState
          (((EvmYul.Yul.State.Ok leftShared leftStore).insert name value).toState.sstore
            slot stored)) =
      Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState tx
        (((EvmYul.Yul.State.Ok rightShared rightStore).insert name value).setState
          (((EvmYul.Yul.State.Ok rightShared rightStore).insert name value).toState.sstore
            slot stored)) := by
  apply projectStorageFromState_eq_of_accountMap_eq
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.insert,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState]
  rw [hState]

private theorem projectStorageFromState_storeHit_initialState_materialized
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (store : EvmYul.Yul.VarStore)
    (arg slot : Nat)
    (hSlot : slot ∈ slots) :
    let initialWithStore : EvmYul.Yul.State :=
      .Ok (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        contract tx storage slots).sharedState store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState tx
        finalState (IRStorageSlot.ofNat slot) =
      (Compiler.Proofs.abstractStoreStorageOrMapping storage 0 arg)
        (IRStorageSlot.ofNat slot) := by
  intro initialWithStore withValue finalState
  simp only [Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.extractStorage,
    finalState, withValue, initialWithStore,
    EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
    EvmYul.Yul.State.toState, EvmYul.Yul.State.insert,
    EvmYul.State.sstore, EvmYul.State.lookupAccount,
    EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
    Compiler.Proofs.YulGeneration.Backends.Native.initialState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
    YulState.initial,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256]
  simp only [Option.option, Std.TreeMap.get?_eq_getElem?,
    Std.TreeMap.getElem?_insert_self]
  by_cases hValueZero :
      (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) = true
  · rw [simpleStorage_account_updateStorage_storage_of_zero _ _ _ hValueZero]
    simp only [IRStorageSlot.toUInt256, IRStorageSlot.ofNat]
    have hArgZeroUInt :
        EvmYul.UInt256.ofNat arg = (⟨0⟩ : EvmYul.UInt256) := by
      cases hArg : EvmYul.UInt256.ofNat arg with
      | mk v =>
          rw [hArg] at hValueZero
          change (v == (0 : Fin EvmYul.UInt256.size)) = true at hValueZero
          have hv : v = (0 : Fin EvmYul.UInt256.size) :=
            of_decide_eq_true hValueZero
          subst hv
          rfl
    have hArgZero : IRStorageWord.ofNat arg = (0 : IRStorageWord) := by
      change EvmYul.UInt256.ofNat arg = (⟨0⟩ : EvmYul.UInt256)
      exact hArgZeroUInt
    by_cases hKey :
        compare (EvmYul.UInt256.ofNat slot) (EvmYul.UInt256.ofNat 0) =
          Ordering.eq
    · have hSlotEq :
          IRStorageSlot.ofNat slot = IRStorageSlot.ofNat 0 := by
        have hUInt :
            EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 :=
          Compiler.Proofs.YulGeneration.Backends.StateBridge.UInt256_eq_of_compare_eq
            hKey
        simpa [IRStorageSlot.ofNat] using hUInt
      have hUInt :
          EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 := by
        simpa [IRStorageSlot.ofNat] using hSlotEq
      have hErase :
          (Std.TreeMap.erase
            (Compiler.Proofs.YulGeneration.Backends.StateBridge.projectStorage
              storage slots)
            (EvmYul.UInt256.ofNat 0))[EvmYul.UInt256.ofNat slot]? =
            none := by
        simpa [Std.TreeMap.get?_eq_getElem?, hUInt] using
          (Std.TreeMap.getElem?_erase_self
            (Compiler.Proofs.YulGeneration.Backends.StateBridge.projectStorage
              storage slots)
            (EvmYul.UInt256.ofNat 0))
      rw [hErase, hUInt]
      simp only [Compiler.Proofs.abstractStoreStorageOrMapping,
        Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, IRStorageSlot.ofNat]
      simp only [if_true]
      rw [hArgZeroUInt]
      rfl
    · have hErase :
          (Std.TreeMap.erase
            (Compiler.Proofs.YulGeneration.Backends.StateBridge.projectStorage
              storage slots)
            (EvmYul.UInt256.ofNat 0))[EvmYul.UInt256.ofNat slot]? =
          (Compiler.Proofs.YulGeneration.Backends.StateBridge.projectStorage
              storage slots)[EvmYul.UInt256.ofNat slot]? := by
        exact simpleStorage_storage_get?_erase_of_ne _ _ _ hKey
      have hLookup :=
        Compiler.Proofs.YulGeneration.Backends.StateBridge.storageLookup_projectStorage_projected
          storage slots slot hSlot
      rw [hErase]
      have hSlotNe :
          IRStorageSlot.ofNat slot ≠ IRStorageSlot.ofNat 0 := by
        intro hEq
        apply hKey
        have hUIntEq :
            EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 := by
          simpa [IRStorageSlot.ofNat] using hEq
        rw [hUIntEq]
        exact Std.ReflCmp.compare_self
      have hSlotNe' :
          EvmYul.UInt256.ofNat slot ≠ IRStorageSlot.ofNat 0 := by
        simpa [IRStorageSlot.ofNat] using hSlotNe
      have hSlotNeUInt :
          EvmYul.UInt256.ofNat slot ≠ EvmYul.UInt256.ofNat 0 := by
        intro hEq
        exact hSlotNe' (by simpa [IRStorageSlot.ofNat] using hEq)
      unfold Compiler.Proofs.YulGeneration.Backends.StateBridge.storageLookup at hLookup
      simp only [Compiler.Proofs.abstractStoreStorageOrMapping,
        IRStorageSlot.ofNat, if_neg hSlotNeUInt]
      unfold Compiler.Proofs.IRGeneration.IRStorageWord
      have hZero : (0 : EvmYul.UInt256) =
          (Inhabited.default : EvmYul.UInt256) := by rfl
      rw [hZero]
      convert hLookup using 1 <;> rfl

  · have hValueNonzero :
        (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) =
          false := by
      cases h :
          (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) <;>
        simp [h] at hValueZero ⊢
    rw [simpleStorage_account_updateStorage_storage_of_nonzero _ _ _
      hValueNonzero]
    simp only [IRStorageSlot.toUInt256, IRStorageSlot.ofNat]
    by_cases hKey :
        compare (EvmYul.UInt256.ofNat slot) (EvmYul.UInt256.ofNat 0) =
          Ordering.eq
    · have hSlotEq :
          IRStorageSlot.ofNat slot = IRStorageSlot.ofNat 0 := by
        have hUInt :
            EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 :=
          Compiler.Proofs.YulGeneration.Backends.StateBridge.UInt256_eq_of_compare_eq
            hKey
        simpa [IRStorageSlot.ofNat] using hUInt
      have hUInt :
          EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 := by
        simpa [IRStorageSlot.ofNat] using hSlotEq
      rw [simpleStorage_storage_get?_insert_of_eq _ _ _ _ hKey]
      rw [hUInt]
      simp [Compiler.Proofs.abstractStoreStorageOrMapping,
        Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, IRStorageSlot.ofNat]
    · rw [simpleStorage_storage_get?_insert_of_ne _ _ _ _ hKey]
      have hLookup :=
        Compiler.Proofs.YulGeneration.Backends.StateBridge.storageLookup_projectStorage_projected
          storage slots slot hSlot
      have hSlotNe :
          IRStorageSlot.ofNat slot ≠ IRStorageSlot.ofNat 0 := by
        intro hEq
        apply hKey
        have hUIntEq :
            EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 := by
          simpa [IRStorageSlot.ofNat] using hEq
        rw [hUIntEq]
        exact Std.ReflCmp.compare_self
      have hSlotNe' :
          EvmYul.UInt256.ofNat slot ≠ IRStorageSlot.ofNat 0 := by
        simpa [IRStorageSlot.ofNat] using hSlotNe
      have hSlotNeUInt :
          EvmYul.UInt256.ofNat slot ≠ EvmYul.UInt256.ofNat 0 := by
        intro hEq
        exact hSlotNe' (by simpa [IRStorageSlot.ofNat] using hEq)
      unfold Compiler.Proofs.YulGeneration.Backends.StateBridge.storageLookup at hLookup
      simp only [Compiler.Proofs.abstractStoreStorageOrMapping,
        IRStorageSlot.ofNat, if_neg hSlotNeUInt]
      unfold Compiler.Proofs.IRGeneration.IRStorageWord
      have hZero : (0 : EvmYul.UInt256) =
          (Inhabited.default : EvmYul.UInt256) := by rfl
      rw [hZero]
      convert hLookup using 1 <;> rfl

private theorem projectStorageFromState_storeHit_markedPrefix_materialized
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (switchId : Nat) (store : EvmYul.Yul.VarStore)
    (arg slot : Nat) (hSlot : slot ∈ slots) :
    let initialWithStore :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
        contract tx storage slots switchId store
    let value := Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg
    let withValue := initialWithStore.insert "value" value
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0) value)
    Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState tx finalState
        (IRStorageSlot.ofNat slot) =
      Compiler.Proofs.abstractStoreStorageOrMapping storage 0 arg (IRStorageSlot.ofNat slot) := by
  intro initialWithStore value withValue finalState
  let markedStore :=
    (((store.insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1))
  have hInitial :=
    projectStorageFromState_storeHit_initialState_materialized
      contract tx storage slots markedStore arg slot hSlot
  have hTransport :=
    projectStorageFromState_insert_sstore_eq_of_toState_eq tx
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        contract tx storage slots)
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        contract tx storage slots).sharedState
      markedStore markedStore "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
      (EvmYul.UInt256.ofNat 0)
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
      (nativeSwitchPostInitFreeMemorySharedState_toState contract tx storage slots)
  change Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState tx
    (((EvmYul.Yul.State.Ok (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage slots) markedStore).insert "value" value).setState
      (((EvmYul.Yul.State.Ok (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        contract tx storage slots) markedStore).insert "value" value).toState.sstore
        (EvmYul.UInt256.ofNat 0) value)) (IRStorageSlot.ofNat slot) = _
  rw [hTransport]
  exact hInitial

private theorem projectStorageFromState_storeHit_postInit_materialized
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (store : EvmYul.Yul.VarStore)
    (arg slot : Nat) (hSlot : slot ∈ slots) :
    let initialWithStore : EvmYul.Yul.State := .Ok
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        contract tx storage slots) store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState tx
        finalState (IRStorageSlot.ofNat slot) =
      (Compiler.Proofs.abstractStoreStorageOrMapping storage 0 arg)
        (IRStorageSlot.ofNat slot) := by
  intro initialWithStore withValue finalState
  have hInitial :=
    projectStorageFromState_storeHit_initialState_materialized
      contract tx storage slots store arg slot hSlot
  have hTransport :=
    projectStorageFromState_insert_sstore_eq_of_toState_eq tx
      (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        contract tx storage slots)
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        contract tx storage slots).sharedState
      store store "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
      (EvmYul.UInt256.ofNat 0)
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
      (nativeSwitchPostInitFreeMemorySharedState_toState contract tx storage slots)
  rw [hTransport]
  exact hInitial

/-- The direct lowered setter halt projects to the same observable storage,
success bit, return value, and logs as the selected IR setter body. -/
private theorem nativeResultsMatchOn_execIRFunction_store0_calldataload4_stop_markedPrefix
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat) (rest : List Nat)
    (hBody : fn.body = [
      Yul.YulStmt.let_ "value" (Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore" [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (hArgs : tx.args = arg :: rest) :
    let yulTx := YulTransaction.ofIR tx
    let slots :=
      Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots
    let initialWithStore :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
        nativeContract yulTx state.storage slots switchId store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩)))) := by
  intro yulTx slots initialWithStore withValue finalState
  have hIR :=
    Compiler.Proofs.IRGeneration.execIRFunction_store0_calldataload4_stop_of_args_cons
      fn tx state arg rest hBody hArgs
  rw [hIR]
  simp only [nativeResultsMatchOn,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeResultsMatchOn]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro slot hslot
    have hslot' : slot ∈ slots := by
      simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
        hslot]
    have hNative :=
      projectStorageFromState_storeHit_markedPrefix_materialized
        nativeContract yulTx state.storage slots switchId store arg slot hslot'
    have hArgMod :
        EvmYul.UInt256.ofNat arg =
          EvmYul.UInt256.ofNat (arg % evmModulus) := by
      unfold EvmYul.UInt256.ofNat
      simp [Id.run, Fin.ofNat, evmModulus, EvmYul.UInt256.size]
    simpa [finalState, withValue, initialWithStore,
      Compiler.Proofs.abstractStoreStorageOrMapping,
      Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, hArgMod] using
      hNative.symm
  · simp [finalState, withValue, initialWithStore,
      Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.Yul.State.sharedState,
      EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
      EvmYul.Yul.State.insert, EvmYul.State.sstore,
      EvmYul.State.setAccount, EvmYul.State.lookupAccount,
      EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage,
      EvmYul.Substate.addAccessedStorageKey, Option.option]
    rfl

/-- Build the direct selected-user-body halt bridge for the generated
`store(uint256)` setter body shape. -/
private theorem NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_store0_calldataload4_stop
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hStoreBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.let_ "value" (Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore" [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest) :
    NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state
      observableSlots := by
  intro nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
    userBodyStart _hLowerRuntime hFind hUserBodyLower _hguards _hArgs
  rcases hArgsCons with ⟨arg, rest, hArgs⟩
  have hBody := hStoreBody fn hFind
  have hLowerConcrete :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames userBodyStart
          ([Yul.YulStmt.let_ "value"
              (Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]),
            Yul.YulStmt.exprStmt
              (Yul.YulExpr.call "sstore"
                [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
            Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])] : List Yul.YulStmt) =
        .ok (simpleStorageLoweredStoreCaseBodyTail3, userBodyStart) := by
    simp [simpleStorageLoweredStoreCaseBodyTail3,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_let,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_expr,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
  have hLowerPair :
      (bodyNative, bodyEnd) = (simpleStorageLoweredStoreCaseBodyTail3, userBodyStart) := by
    rw [hBody, hLowerConcrete] at hUserBodyLower
    simpa using hUserBodyLower.symm
  rcases hLowerPair with ⟨rfl, rfl⟩
  let switchId :=
    Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode irContract) observableSlots
  let initialWithStore :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
      nativeContract yulTx state.storage slots switchId
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
  let withValue := initialWithStore.insert "value"
    (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
  let haltState := withValue.setState
    (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
  let nativeYul :=
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      yulTx state.storage state.events
      (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨0⟩))
  refine ⟨haltState, ⟨0⟩, nativeYul, ?_, rfl, ?_⟩
  · intro _pre suffix
    simpa [switchId, yulTx, slots, initialWithStore, withValue, haltState,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (exec_block_store0_calldataload4_stop_markedPrefix_halt
        (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
          suffix.length)
        nativeContract yulTx state.storage slots switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
        arg rest (by simpa [yulTx, YulTransaction.ofIR] using hArgs))
  · simpa [switchId, yulTx, slots, initialWithStore, withValue, haltState,
      nativeYul,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState] using
      (nativeResultsMatchOn_execIRFunction_store0_calldataload4_stop_markedPrefix
        irContract tx state observableSlots nativeContract fn switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
        arg rest hBody hArgs)

private theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_store0_calldataload4_stop
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hStoreBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.let_ "value" (Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore" [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_halt irContract tx state
    observableSlots
    (NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_store0_calldataload4_stop
      irContract tx state observableSlots hStoreBody hArgsCons)

/-- Closed generated `callDispatcher` theorem for selected store-body success.

This specializes the current public generated-dispatcher theorem to the
lowered `store(uint256)` body shape, discharging the selected user-body halt
bridge from the concrete native body proof above. -/
private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_store0_calldataload4_stop
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (hStoreBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.let_ "value" (Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore" [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap
      (NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_store0_calldataload4_stop
        irContract tx state observableSlots hStoreBody hArgsCons)
      hThreshold

/-- Closed-form evaluation of `projectResult` on the retrieve-hit halt error
produced by the lowered SimpleStorage retrieve body. The halt state is built
by chaining `sload(0)` (toState override), `mstore(0, _)` (toMachineState
override), and `evmReturn(0, 32)` (toMachineState override) starting from a
shared state with empty memory. The native projected return value is the
`Nat`-normalized form of the loaded slot-zero word; storage and logs are
read off the halt's `sharedState` directly. -/
private theorem array_extract_append_left {α} (a b : Array α) :
    (a ++ b).extract 0 a.size = a := by
  apply Array.ext
  · simp
  · intro i hi1 hi2
    simp

private theorem simpleStorage_yulStmtList_length_le_sizeOf :
    (stmts : List Yul.YulStmt) → stmts.length ≤ sizeOf stmts
  | [] => by simp
  | _ :: rest => by
      have hrest := simpleStorage_yulStmtList_length_le_sizeOf rest
      simp
      omega

private theorem byteArray_readWithPadding_prefix
    (source suffix : ByteArray) (hSize : source.size = 32) :
    (⟨source.data ++ suffix.data⟩ : ByteArray).readWithPadding 0 32 = source := by
  have hSizeData : source.data.size = 32 := by
    simpa [-ByteArray.size_data, ByteArray.size] using hSize
  have hSourceNonempty : source.data ≠ #[] := by
    intro h
    have : source.data.size = 0 := by simp [h]
    omega
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  have hSmall : ¬ 32 ≥ 2 ^ 64 := by norm_num
  simp only [hSmall, ↓reduceIte]
  have hAddr : ¬ 0 ≥ (⟨source.data ++ suffix.data⟩ : ByteArray).size := by
    simp [-ByteArray.size_data, ByteArray.size, hSourceNonempty]
  simp only [hAddr, ↓reduceIte]
  have hMin : min 32 (⟨source.data ++ suffix.data⟩ : ByteArray).size = 32 := by
    simp [-ByteArray.size_data, ByteArray.size, hSizeData]
  simp only [hMin]
  apply ByteArray.ext
  simp [-ByteArray.size_data, ByteArray.data_extract, ByteArray.data_append, ByteArray.size,
    ffi.ByteArray.zeroes] at hSizeData ⊢
  rw [show source.data.extract 0 32 = source.data by
    rw [show (32 : Nat) = source.data.size by omega]
    exact array_extract_append_left source.data #[]]
  rw [show min 32 source.data.size = 32 by omega]
  rw [show 32 - source.data.size = 0 by omega]
  rw [show min 0 suffix.data.size = 0 by omega]
  simp

private theorem byteArray_append_zeroes_zero (source : ByteArray) :
    source ++ ffi.ByteArray.zeroes (OfNat.ofNat 0) = source := by
  apply ByteArray.ext
  simp [ByteArray.data_append, ffi.ByteArray.zeroes]

private theorem byteArray_extract_zero_32_eq_of_size
    (source : ByteArray) (hSize : source.size = 32) :
    source.extract 0 32 = source := by
  apply ByteArray.ext
  simp [-ByteArray.size_data, ByteArray.data_extract, ByteArray.size] at hSize ⊢
  rw [hSize]
  simp

private theorem byteArray_write_zero_32_readWithPadding_eq_of_size
    (source dest : ByteArray) (hSize : source.size = 32)
    (hDest : 32 ≤ dest.size) :
    (source.write 0 dest 0 32).readWithPadding 0 32 = source := by
  unfold ByteArray.write
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  have hSourceAddr : ¬ 0 ≥ source.size := by omega
  simp only [hSourceAddr, ↓reduceIte]
  have hPractical : min 32 (source.size - 0) = 32 := by omega
  have hEnd : min dest.size (0 + 32) = 32 := by omega
  have hSourcePaddingLength : 32 - (0 + 32) = 0 := by omega
  have hDestPaddingLength : 0 - dest.size = 0 := by simp
  simp only [hPractical, hEnd, hSourcePaddingLength, hDestPaddingLength]
  have hCopy :
      (source ++ ffi.ByteArray.zeroes { toBitVec := 0 }).copySlice 0
        (dest ++ ffi.ByteArray.zeroes { toBitVec := 0 }) 0 (32 + 0) =
        (⟨source.data ++ (dest.extract 32 dest.size).data⟩ : ByteArray) := by
    rw [ByteArray.copySlice_eq_append]
    simp [ffi.ByteArray.zeroes, ByteArray.data_append, ByteArray.data_extract,
      -ByteArray.size_data, ByteArray.size, hSize]
    have hSourceZero : source ++ ({ data := #[] } : ByteArray) = source := by
      simpa [ffi.ByteArray.zeroes] using byteArray_append_zeroes_zero source
    have hDestZero : dest ++ ({ data := #[] } : ByteArray) = dest := by
      simpa [ffi.ByteArray.zeroes] using byteArray_append_zeroes_zero dest
    rw [hSourceZero, hDestZero, byteArray_extract_zero_32_eq_of_size source hSize]
    apply ByteArray.ext
    simp [ByteArray.data_append, ByteArray.data_extract]
    rw [show min 32 source.size = 32 by omega]
  have hPrefix :=
    byteArray_readWithPadding_prefix source (dest.extract 32 dest.size) hSize
  rw [← hCopy] at hPrefix
  simpa using hPrefix

private theorem byteArray_write_empty_64_32_size_ge_32
    (source : ByteArray) (hSize : source.size = 32) :
    32 ≤ (source.write 0 ByteArray.empty 64 32).size := by
  unfold ByteArray.write
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  have hSourceAddr : ¬ 0 ≥ source.size := by omega
  simp only [hSourceAddr, ↓reduceIte]
  have hPractical : min 32 (source.size - 0) = 32 := by omega
  have hEnd : min ByteArray.empty.size (64 + 32) = 0 := by simp
  have hSourcePaddingLength : 0 - (64 + 32) = 0 := by omega
  have hDestPaddingLength : 64 - ByteArray.empty.size = 64 := by simp
  simp only [hPractical, hEnd, hSourcePaddingLength, hDestPaddingLength]
  rw [ByteArray.copySlice_eq_append]
  simp [ffi.ByteArray.zeroes, ByteArray.data_append, ByteArray.data_extract,
    -ByteArray.size_data, ByteArray.size, hSize]
  norm_num
  omega

private theorem nativeSwitchPostInitFreeMemorySharedState_memory_size_ge_32
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    32 ≤ (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).memory.size := by
  simp [Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    Compiler.Proofs.YulGeneration.Backends.Native.initialState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.mkBlockHeader,
    Compiler.Constants.freeMemoryPointer, YulState.initial,
    EvmYul.Yul.State.sharedState, EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes]
  exact byteArray_write_empty_64_32_size_ge_32
    (EvmYul.UInt256.ofNat 128).toByteArray
    (Compiler.Proofs.YulGeneration.Backends.Native.uint256_toByteArray_size
      (EvmYul.UInt256.ofNat 128))

private theorem nativeSwitchPostInitFreeMemorySharedState_accountMap
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).accountMap =
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        contract tx storage observableSlots).sharedState.accountMap := by
  rfl

private theorem mstore0_then_return32_hReturn_eq_toByteArray
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemorySize : 32 ≤ sharedState.memory.size) :
    let state : EvmYul.Yul.State := .Ok sharedState store
    let stored :=
      state.setMachineState
        (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)
    let returned :=
      stored.setMachineState
        (stored.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32))
    returned.sharedState.H_return = value.toByteArray := by
  dsimp
  simp only [EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.setMachineState,
    EvmYul.Yul.State.sharedState]
  simp only [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    EvmYul.writeBytes, EvmYul.MachineState.evmReturn]
  exact byteArray_write_zero_32_readWithPadding_eq_of_size value.toByteArray
    sharedState.memory
    (Compiler.Proofs.YulGeneration.Backends.Native.uint256_toByteArray_size value)
    hMemorySize

private theorem projectResult_retrieveHit_eq
    (tx : YulTransaction) (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hMemorySize : 32 ≤ shared.memory.size) :
    let p := shared.sload (EvmYul.UInt256.ofNat 0)
    let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
    let shared3 : EvmYul.SharedState .Yul :=
      { shared2 with
        toMachineState :=
          shared2.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        tx initialStorage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt
          (EvmYul.Yul.State.Ok shared3 store) ⟨1⟩)) =
      { success := true,
        returnValue := some p.2.toNat,
        finalStorage :=
          Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
            tx (EvmYul.Yul.State.Ok shared3 store),
        finalMappings :=
          Compiler.Proofs.storageAsMappings
            (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              tx (EvmYul.Yul.State.Ok shared3 store)),
        events :=
          initialEvents ++
            Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
              (EvmYul.Yul.State.Ok shared3 store) } := by
  intro p shared1 shared2 shared3
  -- The harness helpers describe the result via `setMachineState` chains;
  -- those equal the structural overrides used in `shared3`.
  have hSize :
      (EvmYul.Yul.State.Ok shared3 store).sharedState.H_return.size = 32 := by
    have h := Compiler.Proofs.YulGeneration.Backends.Native.mstore0_then_return32_hReturn_size
      shared1 store p.2
    simpa [shared3, shared2, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.sharedState] using h
  have hH_return :
      (EvmYul.Yul.State.Ok shared3 store).sharedState.H_return = p.2.toByteArray := by
    have h :=
      mstore0_then_return32_hReturn_eq_toByteArray shared1 store p.2
        (by simpa [shared1] using hMemorySize)
    simpa [shared3, shared2, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.sharedState] using h
  have hHaltNotZero : (⟨1⟩ : EvmYul.Yul.Ast.Literal) ≠ ⟨0⟩ := by
    intro h
    norm_num [EvmYul.UInt256.size] at h
  have hReturnValue :
      Compiler.Proofs.YulGeneration.Backends.Native.projectHaltReturn
          (EvmYul.Yul.State.Ok shared3 store) ⟨1⟩ = some p.2.toNat := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.projectHaltReturn_32ByteReturn
      (EvmYul.Yul.State.Ok shared3 store) ⟨1⟩ hHaltNotZero hSize]
    rw [hH_return,
      Compiler.Proofs.YulGeneration.Backends.Native.byteArrayWord_uint256_toByteArray]
  simp only [Compiler.Proofs.YulGeneration.Backends.Native.projectResult,
    hReturnValue]

/-- Closed-form evaluation of `projectResult` on a selected literal-return
body halt produced by native `mstore(0, value); return(0, 32)`. -/
private theorem projectResult_literalReturnHit_eq
    (tx : YulTransaction) (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (value : Nat) (hMemorySize : 32 ≤ shared.memory.size) :
    let shared1 : EvmYul.SharedState .Yul :=
      { shared with
        toMachineState :=
          shared.toMachineState.mstore
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat value) }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        tx initialStorage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt
          (EvmYul.Yul.State.Ok shared2 store) ⟨1⟩)) =
      { success := true,
        returnValue := some (EvmYul.UInt256.ofNat value).toNat,
        finalStorage :=
          Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
            tx (EvmYul.Yul.State.Ok shared2 store),
        finalMappings :=
          Compiler.Proofs.storageAsMappings
            (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              tx (EvmYul.Yul.State.Ok shared2 store)),
        events :=
          initialEvents ++
            Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
              (EvmYul.Yul.State.Ok shared2 store) } := by
  intro shared1 shared2
  have hSize :
      (EvmYul.Yul.State.Ok shared2 store).sharedState.H_return.size = 32 := by
    have h := Compiler.Proofs.YulGeneration.Backends.Native.mstore0_then_return32_hReturn_size
      shared store (EvmYul.UInt256.ofNat value)
    simpa [shared2, shared1, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.sharedState] using h
  have hH_return :
      (EvmYul.Yul.State.Ok shared2 store).sharedState.H_return =
        (EvmYul.UInt256.ofNat value).toByteArray := by
    have h :=
      mstore0_then_return32_hReturn_eq_toByteArray shared store
        (EvmYul.UInt256.ofNat value) hMemorySize
    simpa [shared2, shared1, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.sharedState] using h
  have hHaltNotZero : (⟨1⟩ : EvmYul.Yul.Ast.Literal) ≠ ⟨0⟩ := by
    intro h
    norm_num [EvmYul.UInt256.size] at h
  have hReturnValue :
      Compiler.Proofs.YulGeneration.Backends.Native.projectHaltReturn
          (EvmYul.Yul.State.Ok shared2 store) ⟨1⟩ =
        some (EvmYul.UInt256.ofNat value).toNat := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.projectHaltReturn_32ByteReturn
      (EvmYul.Yul.State.Ok shared2 store) ⟨1⟩ hHaltNotZero hSize]
    rw [hH_return,
      Compiler.Proofs.YulGeneration.Backends.Native.byteArrayWord_uint256_toByteArray]
  simp only [Compiler.Proofs.YulGeneration.Backends.Native.projectResult,
    hReturnValue]

/-- The direct lowered retrieve halt projects to the same observable result as
the selected IR retrieve body. -/
private theorem nativeResultsMatchOn_execIRFunction_mstore0_sload0_return32_markedPrefix
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (hBody : fn.body = [
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    let yulTx := YulTransaction.ofIR tx
    let slots :=
      Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots
    let markedStore :=
      (((store.insert
        (Backends.nativeSwitchDiscrTempName switchId)
        (EvmYul.UInt256.ofNat
          (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1))
    let shared :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        nativeContract yulTx state.storage slots
    let p := shared.sload (EvmYul.UInt256.ofNat 0)
    let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
    let shared3 : EvmYul.SharedState .Yul :=
      { shared2 with
        toMachineState :=
          shared2.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared3 markedStore) ⟨1⟩)))) := by
  intro yulTx slots markedStore shared p shared1 shared2 shared3
  have hIR :=
    Compiler.Proofs.IRGeneration.execIRFunction_mstore0_sload0_return32
      fn tx state hBody
  have hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared3 markedStore) ⟨1⟩)) =
        { success := true,
          returnValue := some p.2.toNat,
          finalStorage :=
            Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              yulTx (EvmYul.Yul.State.Ok shared3 markedStore),
          finalMappings :=
            Compiler.Proofs.storageAsMappings
              (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
                yulTx (EvmYul.Yul.State.Ok shared3 markedStore)),
          events :=
            state.events ++
              Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
                (EvmYul.Yul.State.Ok shared3 markedStore) } := by
    have hMemorySize : 32 ≤ shared.memory.size := by
      simpa [shared] using
        nativeSwitchPostInitFreeMemorySharedState_memory_size_ge_32
          nativeContract yulTx state.storage slots
    simpa [yulTx, shared, p, shared1, shared2, shared3] using
      projectResult_retrieveHit_eq yulTx state.storage state.events
        shared markedStore hMemorySize
  have hSlotZero : 0 ∈ slots := by
    simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots]
  have hp :
      p.2 = state.storage (IRStorageSlot.ofNat 0) := by
    have hload :=
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_sload_materializedSlot_value
        nativeContract yulTx state.storage slots 0 hSlotZero
    change (EvmYul.State.sload
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        nativeContract yulTx state.storage slots).toState
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 0)).2 =
        state.storage (IRStorageSlot.ofNat 0)
    exact hload
  have hLogs :
      Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
        (EvmYul.Yul.State.Ok shared3 markedStore) = [] := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
      shared3, shared2, shared1, p, shared,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.State.sload, EvmYul.State.addAccessedStorageKey,
      EvmYul.Substate.addAccessedStorageKey, EvmYul.Yul.State.sharedState]
    rfl
  rw [hIR, hProject]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [hp, Compiler.Proofs.IRGeneration.IRStorageWord.toNat]
  · intro slot hslot
    have hslot' : slot ∈ slots := by
      simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
        hslot]
    have hNative :=
      Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState_retrieveHit_initialState_materialized
        nativeContract yulTx state.storage slots markedStore slot hslot'
    exact hNative.symm
  · rw [hLogs, List.append_nil]

/-- Generated zero-parameter literal-return functions first run
    `genParamLoads []`, whose calldata guard skips for well-sized ABI calldata,
    then execute the literal-return payload. -/
private theorem execIRFunction_zeroParam_mstore0_lit_return32
    (fn : IRFunction) (tx : IRTransaction) (initialState : IRState)
    (value : Nat)
    (hParams : fn.params = [])
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : fn.body =
      Compiler.CompilationModel.genParamLoads [] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
       Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    execIRFunction fn tx.args (applyIRTransactionContext tx initialState) =
      { success := true
        returnValue := some value
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events } := by
  let rest : List Yul.YulStmt :=
    [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
      [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
     Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
      [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]
  let params : List CompilationModel.Param := []
  let body := Compiler.CompilationModel.genParamLoads params ++ rest
  unfold execIRFunction
  simp only [hParams, hBody, List.zip_nil_left]
  change
    (match execIRStmts (sizeOf body + 1)
        (applyIRTransactionContext tx initialState) body with
      | .continue s =>
          ({
            success := true
            returnValue := s.returnValue
            finalStorage := s.storage
            finalMappings := Compiler.Proofs.storageAsMappings s.storage
            events := s.events } : IRResult)
      | .return v s =>
          ({
            success := true
            returnValue := some v
            finalStorage := s.storage
            finalMappings := Compiler.Proofs.storageAsMappings s.storage
            events := s.events } : IRResult)
      | .stop s =>
          ({
            success := true
            returnValue := none
            finalStorage := s.storage
            finalMappings := Compiler.Proofs.storageAsMappings s.storage
            events := s.events } : IRResult)
      | .revert _ =>
          ({
            success := false
            returnValue := none
            finalStorage := (applyIRTransactionContext tx initialState).storage
            finalMappings :=
              Compiler.Proofs.storageAsMappings
                (applyIRTransactionContext tx initialState).storage
            events := (applyIRTransactionContext tx initialState).events } : IRResult)) =
      ({
        success := true
        returnValue := some value
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events } : IRResult)
  have hFuel :
      sizeOf body + 1 =
        (Compiler.CompilationModel.genParamLoads params).length + rest.length +
          (sizeOf body - body.length) + 1 := by
    have hBodyLength :
        body.length = (Compiler.CompilationModel.genParamLoads params).length +
          rest.length := by
      simp [body]
    have hSize := simpleStorage_yulStmtList_length_le_sizeOf body
    omega
  have hParam :
      execIRStmts
        ((Compiler.CompilationModel.genParamLoads params).length +
            rest.length + (sizeOf body - body.length) + 1)
        (applyIRTransactionContext tx initialState)
        body =
      execIRStmts
        (rest.length + (sizeOf body - body.length) +
          1)
        (Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState
          (applyIRTransactionContext tx initialState) [])
        rest := by
    simpa [params, body] using
      Compiler.Proofs.IRGeneration.ParamLoading.exec_genParamLoads_supported_then_extraFuel
        (state := applyIRTransactionContext tx initialState)
        (params := params) (bindings := []) (rest := rest)
        (extraFuel := sizeOf body - body.length)
        (by intro param hmem; simp [params] at hmem)
        (by
          simpa [Compiler.Constants.evmModulus, EvmYul.UInt256.size,
            applyIRTransactionContext] using hNoWrap)
        (by simp [params, SourceSemantics.bindSupportedParams])
  have hRaw :
      execIRStmts (rest.length + (sizeOf body - body.length) + 1)
        (Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState
          (applyIRTransactionContext tx initialState) [])
        rest =
        .return value
          { (applyIRTransactionContext tx initialState) with
            memory := fun o => if o = 0 then value else
              (applyIRTransactionContext tx initialState).memory o } := by
    have hEnough : 2 ≤ rest.length + (sizeOf body - body.length) := by
      simp [rest]
    obtain ⟨k, hk⟩ :
        ∃ k, rest.length + (sizeOf body - body.length) = k + 2 :=
      ⟨rest.length + (sizeOf body - body.length) - 2, by omega⟩
    rw [hk]
    simp +decide [Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState,
      rest, execIRStmts, execIRStmt, evalIRExpr]
  rw [hFuel, hParam, hRaw]
  simp [applyIRTransactionContext]

/-- Generated zero-parameter storage-return functions first run
    `genParamLoads []`, whose calldata guard skips for well-sized ABI calldata,
    then execute the storage-return payload. -/
private theorem execIRFunction_zeroParam_mstore0_sload0_return32
    (fn : IRFunction) (tx : IRTransaction) (initialState : IRState)
    (hParams : fn.params = [])
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : fn.body =
      Compiler.CompilationModel.genParamLoads [] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
       Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    execIRFunction fn tx.args (applyIRTransactionContext tx initialState) =
      { success := true
        returnValue := some ((initialState.storage (IRStorageSlot.ofNat 0)).toNat)
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events } := by
  let rest : List Yul.YulStmt :=
    [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
      [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
     Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
      [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]
  let params : List CompilationModel.Param := []
  let body := Compiler.CompilationModel.genParamLoads params ++ rest
  unfold execIRFunction
  simp only [hParams, hBody, List.zip_nil_left]
  change
    (match execIRStmts (sizeOf body + 1)
        (applyIRTransactionContext tx initialState) body with
      | .continue s =>
          ({
            success := true
            returnValue := s.returnValue
            finalStorage := s.storage
            finalMappings := Compiler.Proofs.storageAsMappings s.storage
            events := s.events } : IRResult)
      | .return v s =>
          ({
            success := true
            returnValue := some v
            finalStorage := s.storage
            finalMappings := Compiler.Proofs.storageAsMappings s.storage
            events := s.events } : IRResult)
      | .stop s =>
          ({
            success := true
            returnValue := none
            finalStorage := s.storage
            finalMappings := Compiler.Proofs.storageAsMappings s.storage
            events := s.events } : IRResult)
      | .revert _ =>
          ({
            success := false
            returnValue := none
            finalStorage := (applyIRTransactionContext tx initialState).storage
            finalMappings :=
              Compiler.Proofs.storageAsMappings
                (applyIRTransactionContext tx initialState).storage
            events := (applyIRTransactionContext tx initialState).events } : IRResult)) =
      ({
        success := true
        returnValue := some ((initialState.storage (IRStorageSlot.ofNat 0)).toNat)
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events } : IRResult)
  have hFuel :
      sizeOf body + 1 =
        (Compiler.CompilationModel.genParamLoads params).length + rest.length +
          (sizeOf body - body.length) + 1 := by
    have hBodyLength :
        body.length = (Compiler.CompilationModel.genParamLoads params).length +
          rest.length := by
      simp [body]
    have hSize := simpleStorage_yulStmtList_length_le_sizeOf body
    omega
  have hParam :
      execIRStmts
        ((Compiler.CompilationModel.genParamLoads params).length +
            rest.length + (sizeOf body - body.length) + 1)
        (applyIRTransactionContext tx initialState)
        body =
      execIRStmts
        (rest.length + (sizeOf body - body.length) +
          1)
        (Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState
          (applyIRTransactionContext tx initialState) [])
        rest := by
    simpa [params, body] using
      Compiler.Proofs.IRGeneration.ParamLoading.exec_genParamLoads_supported_then_extraFuel
        (state := applyIRTransactionContext tx initialState)
        (params := params) (bindings := []) (rest := rest)
        (extraFuel := sizeOf body - body.length)
        (by intro param hmem; simp [params] at hmem)
        (by
          simpa [Compiler.Constants.evmModulus, EvmYul.UInt256.size,
            applyIRTransactionContext] using hNoWrap)
        (by simp [params, SourceSemantics.bindSupportedParams])
  have hRaw :
      execIRStmts (rest.length + (sizeOf body - body.length) + 1)
        (Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState
          (applyIRTransactionContext tx initialState) [])
        rest =
        .return
          (((applyIRTransactionContext tx initialState).storage
            (IRStorageSlot.ofNat 0)).toNat)
          { (applyIRTransactionContext tx initialState) with
            memory := fun o => if o = 0 then
              (((applyIRTransactionContext tx initialState).storage
                (IRStorageSlot.ofNat 0)).toNat)
              else (applyIRTransactionContext tx initialState).memory o } := by
    have hEnough : 2 ≤ rest.length + (sizeOf body - body.length) := by
      simp [rest]
    obtain ⟨k, hk⟩ :
        ∃ k, rest.length + (sizeOf body - body.length) = k + 2 :=
      ⟨rest.length + (sizeOf body - body.length) - 2, by omega⟩
    rw [hk]
    simp +decide [Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState,
      rest, execIRStmts, execIRStmt, evalIRExpr, evalIRCall_sload_singleton,
      Compiler.Proofs.abstractLoadStorageOrMapping]
  rw [hFuel, hParam, hRaw]
  simp [applyIRTransactionContext]

set_option maxRecDepth 10000

/-- Generated one-argument setter functions first run
    `genParamLoads [{name := "value", ty := .uint256}]`, then store the decoded
    value in slot zero and stop. -/
private theorem execIRFunction_oneParam_store0_value_stop
    (fn : IRFunction) (tx : IRTransaction) (initialState : IRState)
    (arg : Nat) (rest : List Nat)
    (hParams :
      fn.params =
        [{ name := "value", ty := IRType.uint256 }])
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : tx.args = arg :: rest)
    (hBody : fn.body =
      Compiler.CompilationModel.genParamLoads
        [{ name := "value", ty := CompilationModel.ParamType.uint256 }] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
       Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])]) :
    execIRFunction fn tx.args (applyIRTransactionContext tx initialState) =
      { success := true
        returnValue := none
        finalStorage :=
          Compiler.Proofs.abstractStoreStorageOrMapping initialState.storage 0
            (arg % Compiler.Constants.evmModulus)
        finalMappings :=
          Compiler.Proofs.storageAsMappings
            (Compiler.Proofs.abstractStoreStorageOrMapping initialState.storage 0
              (arg % Compiler.Constants.evmModulus))
        events := initialState.events } := by
  let params : List CompilationModel.Param :=
    [{ name := "value", ty := CompilationModel.ParamType.uint256 }]
  let irParams : List IRParam :=
    [{ name := "value", ty := IRType.uint256 }]
  let restBody : List Yul.YulStmt :=
    [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
      [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
     Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])]
  let body := Compiler.CompilationModel.genParamLoads params ++ restBody
  let txState := applyIRTransactionContext tx initialState
  let stateWithParams :=
    ((irParams.zip tx.args).foldl
      (fun s pair => s.setVar pair.1.name pair.2) txState)
  unfold execIRFunction
  simp only [hParams, hBody]
  change
    (match execIRStmts (sizeOf body + 1) stateWithParams body with
      | .continue s =>
          ({
            success := true
            returnValue := s.returnValue
            finalStorage := s.storage
            finalMappings := Compiler.Proofs.storageAsMappings s.storage
            events := s.events } : IRResult)
      | .return v s =>
          ({
            success := true
            returnValue := some v
            finalStorage := s.storage
            finalMappings := Compiler.Proofs.storageAsMappings s.storage
            events := s.events } : IRResult)
      | .stop s =>
          ({
            success := true
            returnValue := none
            finalStorage := s.storage
            finalMappings := Compiler.Proofs.storageAsMappings s.storage
            events := s.events } : IRResult)
      | .revert _ =>
          ({
            success := false
            returnValue := none
            finalStorage := txState.storage
            finalMappings := Compiler.Proofs.storageAsMappings txState.storage
            events := txState.events } : IRResult)) =
      ({
        success := true
        returnValue := none
        finalStorage :=
          Compiler.Proofs.abstractStoreStorageOrMapping initialState.storage 0
            (arg % Compiler.Constants.evmModulus)
        finalMappings :=
          Compiler.Proofs.storageAsMappings
            (Compiler.Proofs.abstractStoreStorageOrMapping initialState.storage 0
              (arg % Compiler.Constants.evmModulus))
        events := initialState.events } : IRResult)
  have hFuel :
      sizeOf body + 1 =
        (Compiler.CompilationModel.genParamLoads params).length +
          restBody.length + (sizeOf body - body.length) + 1 := by
    have hBodyLength :
        body.length = (Compiler.CompilationModel.genParamLoads params).length +
          restBody.length := by
      simp [body]
    have hSize := simpleStorage_yulStmtList_length_le_sizeOf body
    omega
  have hBind :
      SourceSemantics.bindSupportedParams params stateWithParams.calldata =
        some [("value", arg % Compiler.Constants.evmModulus)] := by
    simp [params, stateWithParams, txState, hArgs, applyIRTransactionContext,
      SourceSemantics.bindSupportedParams,
      SourceSemantics.decodeSupportedParamWord, Compiler.Constants.evmModulus]
  have hParam :
      execIRStmts
        ((Compiler.CompilationModel.genParamLoads params).length +
            restBody.length + (sizeOf body - body.length) + 1)
        stateWithParams body =
      execIRStmts
        (restBody.length + (sizeOf body - body.length) + 1)
        (Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState
          stateWithParams [("value", arg % Compiler.Constants.evmModulus)])
        restBody := by
    simpa [params, body] using
      Compiler.Proofs.IRGeneration.ParamLoading.exec_genParamLoads_supported_then_extraFuel
        (state := stateWithParams)
        (params := params)
        (bindings := [("value", arg % Compiler.Constants.evmModulus)])
        (rest := restBody)
        (extraFuel := sizeOf body - body.length)
        (by
          intro param hmem
          simp [params] at hmem
          subst param
          simp [SupportedExternalScalarParamType])
        (by
          simpa [Compiler.Constants.evmModulus, EvmYul.UInt256.size,
            stateWithParams, txState, applyIRTransactionContext] using hNoWrap)
        hBind
  have hRaw :
      execIRStmts
        (restBody.length + (sizeOf body - body.length) + 1)
        (Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState
          stateWithParams [("value", arg % Compiler.Constants.evmModulus)])
        restBody =
        .stop
          { Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState
              stateWithParams [("value", arg % Compiler.Constants.evmModulus)] with
            storage :=
              Compiler.Proofs.abstractStoreStorageOrMapping
                (Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState
                  stateWithParams [("value", arg % Compiler.Constants.evmModulus)]).storage
                0 (arg % Compiler.Constants.evmModulus) } := by
    have hEnough : 2 ≤ restBody.length + (sizeOf body - body.length) := by
      simp [restBody]
    obtain ⟨k, hk⟩ :
        ∃ k, restBody.length + (sizeOf body - body.length) = k + 2 :=
      ⟨restBody.length + (sizeOf body - body.length) - 2, by omega⟩
    rw [hk]
    simp +decide [Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState,
      restBody, execIRStmts, execIRStmt, evalIRExpr, IRState.getVar,
      IRState.setVar]
  rw [hFuel, hParam, hRaw]
  simp [Compiler.Proofs.IRGeneration.ParamLoading.applyBindingsToIRState,
    stateWithParams, txState, applyIRTransactionContext, IRState.setVar,
    irParams, hArgs, Compiler.Proofs.abstractStoreStorageOrMapping_eq]

/-- The generated one-argument setter halt projects to the same observable
storage, success bit, return value, and logs as the selected generated IR
setter body. -/
private theorem nativeResultsMatchOn_execIRFunction_oneParam_store0_value_stop_markedPrefix
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat) (rest : List Nat)
    (hParams :
      fn.params =
        [{ name := "value", ty := IRType.uint256 }])
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : tx.args = arg :: rest)
    (hBody : fn.body =
      Compiler.CompilationModel.genParamLoads
        [{ name := "value", ty := CompilationModel.ParamType.uint256 }] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
       Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])]) :
    let yulTx := YulTransaction.ofIR tx
    let slots :=
      Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots
    let initialWithStore :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
        nativeContract yulTx state.storage slots switchId store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩)))) := by
  intro yulTx slots initialWithStore withValue finalState
  have hIR :=
    execIRFunction_oneParam_store0_value_stop
      fn tx state arg rest hParams hNoWrap hArgs hBody
  rw [hIR]
  simp only [nativeResultsMatchOn,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeResultsMatchOn]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro slot hslot
    have hslot' : slot ∈ slots := by
      simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
        hslot]
    have hNative :=
      projectStorageFromState_storeHit_markedPrefix_materialized
        nativeContract yulTx state.storage slots switchId store arg slot hslot'
    have hArgMod :
        EvmYul.UInt256.ofNat arg =
          EvmYul.UInt256.ofNat (arg % evmModulus) := by
      unfold EvmYul.UInt256.ofNat
      simp [Id.run, Fin.ofNat, evmModulus, EvmYul.UInt256.size]
    simpa [finalState, withValue, initialWithStore,
      Compiler.Proofs.abstractStoreStorageOrMapping,
      Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, hArgMod] using
      hNative.symm
  · simp [finalState, withValue, initialWithStore,
      Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.Yul.State.sharedState,
      EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
      EvmYul.Yul.State.insert, EvmYul.State.sstore,
      EvmYul.State.setAccount, EvmYul.State.lookupAccount,
      EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage,
      EvmYul.Substate.addAccessedStorageKey, Option.option]
    rfl

/-- Build the selected-user-body halt bridge for generated one-argument
`store(uint256)` setter bodies. -/
private theorem NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_oneParam_store0_value_stop
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hParams :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.params = [{ name := "value", ty := IRType.uint256 }])
    (hStoreBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body =
          Compiler.CompilationModel.genParamLoads
            [{ name := "value", ty := CompilationModel.ParamType.uint256 }] ++
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
           Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest) :
    NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state
      observableSlots := by
  intro nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
    userBodyStart _hLowerRuntime hFind hUserBodyLower _hguards _hArgs
  rcases hArgsCons with ⟨arg, rest, hArgs⟩
  have hFnParams := hParams fn hFind
  have hBody := hStoreBody fn hFind
  have hLowerConcrete :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames userBodyStart
          (Compiler.CompilationModel.genParamLoads
            [{ name := "value", ty := CompilationModel.ParamType.uint256 }] ++
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
           Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])] : List Yul.YulStmt) =
        .ok (simpleStorageLoweredStoreCaseBodyTail2, userBodyStart) := by
    simp [simpleStorageLoweredStoreCaseBodyTail2,
      Compiler.CompilationModel.genParamLoads,
      Compiler.CompilationModel.genParamLoadsFrom,
      Compiler.CompilationModel.genParamLoadBodyFrom,
      Compiler.CompilationModel.genSingleParamLoad,
      Compiler.CompilationModel.genScalarLoad,
      Compiler.CompilationModel.paramHeadSize,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_expr,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_if,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_let,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
  have hLowerPair :
      (bodyNative, bodyEnd) =
        (simpleStorageLoweredStoreCaseBodyTail2, userBodyStart) := by
    rw [hBody, hLowerConcrete] at hUserBodyLower
    simpa using hUserBodyLower.symm
  rcases hLowerPair with ⟨rfl, rfl⟩
  let switchId :=
    Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode irContract) observableSlots
  let markedStore :=
    (((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore.insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1))
  let shared :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      nativeContract yulTx state.storage slots
  let initialWithStore : EvmYul.Yul.State := .Ok shared markedStore
  let withValue := initialWithStore.insert "value"
    (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
  let haltState := withValue.setState
    (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
  let nativeYul :=
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      yulTx state.storage state.events
      (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨0⟩))
  refine ⟨haltState, ⟨0⟩, nativeYul, ?_, rfl, ?_⟩
  · intro _pre suffix
    have hExec :=
      exec_block_simpleStorageLoweredStoreCaseBodyTail2_markedPrefix_halt
        (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
          suffix.length)
        nativeContract yulTx state.storage slots switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
        arg rest (by simpa [yulTx, YulTransaction.ofIR] using hArgs)
        (by simpa [yulTx, YulTransaction.ofIR_args] using hNoWrap)
    change
      EvmYul.Yul.exec
          (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
              suffix.length + 10)
          (.Block simpleStorageLoweredStoreCaseBodyTail2)
          (some nativeContract) (EvmYul.Yul.State.Ok shared markedStore) =
        .error (EvmYul.Yul.Exception.YulHalt haltState ⟨0⟩)
    simpa [switchId, yulTx, slots, markedStore, shared, initialWithStore,
      withValue, haltState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hExec
  · have hInitial :
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
            nativeContract yulTx state.storage slots switchId
            Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore =
          initialWithStore := by
      rfl
    have hMatch :=
      nativeResultsMatchOn_execIRFunction_oneParam_store0_value_stop_markedPrefix
        irContract tx state observableSlots nativeContract fn switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
        arg rest hFnParams hNoWrap hArgs hBody
    dsimp only at hMatch
    rw [hInitial] at hMatch
    simpa [nativeYul, haltState, withValue] using hMatch

private theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_oneParam_store0_value_stop
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hParams :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.params = [{ name := "value", ty := IRType.uint256 }])
    (hStoreBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body =
          Compiler.CompilationModel.genParamLoads
            [{ name := "value", ty := CompilationModel.ParamType.uint256 }] ++
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
           Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_halt irContract tx state
    observableSlots
    (NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_oneParam_store0_value_stop
      irContract tx state observableSlots hNoWrap hParams hStoreBody hArgsCons)

private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_oneParam_store0_value_stop
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (hParams :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.params = [{ name := "value", ty := IRType.uint256 }])
    (hStoreBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body =
          Compiler.CompilationModel.genParamLoads
            [{ name := "value", ty := CompilationModel.ParamType.uint256 }] ++
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
           Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap
      (NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_oneParam_store0_value_stop
        irContract tx state observableSlots hNoWrap hParams hStoreBody hArgsCons)
      hThreshold

private theorem selectedCompiledFunction_oneParam_store0_value_stop_shape_of_forall₂
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef)
    (tx : IRTransaction)
    {pairs : List (CompilationModel.FunctionSpec × Nat)}
    {irFns : List IRFunction}
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          CompilationModel.compileFunctionSpec fields events errors
            [] entry.2 entry.1 = Except.ok irFn)
        pairs irFns)
    (hSourceParams :
      ∀ entry, entry ∈ pairs → entry.2 = tx.functionSelector →
        entry.1.params =
          [{ name := "value", ty := CompilationModel.ParamType.uint256 }])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ pairs →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList fields events errors .calldata
          [] false (entry.1.params.map (·.name)) [] entry.1.body =
            Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (irFn : IRFunction)
    (hFind :
      irFns.find? (fun fn => fn.selector == tx.functionSelector) =
        some irFn) :
    irFn.params = [{ name := "value", ty := IRType.uint256 }] ∧
    irFn.body =
      Compiler.CompilationModel.genParamLoads
        [{ name := "value", ty := CompilationModel.ParamType.uint256 }] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])] := by
  induction hcompiled with
  | nil =>
      simp at hFind
  | @cons entry headIr tailPairs tailIr hhead htail ih =>
      by_cases hSelector : headIr.selector = tx.functionSelector
      · simp [hSelector] at hFind
        rcases hFind with rfl
        have hEntrySelector : entry.2 = tx.functionSelector := by
          have hSel :=
            Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_selector
              fields events errors entry.2 entry.1 headIr hhead
          simpa [hSelector] using hSel.symm
        rcases
            Compiler.Proofs.IRGeneration.FunctionShape.compileFunctionSpec_ok_components
              fields events errors entry.2 entry.1 headIr hhead with
          ⟨returns, bodyStmts, _hvalidate, _hreturns, hbody, hirFn⟩
        have hEntryMem : entry ∈ entry :: tailPairs := by simp
        have hSpecParams :
            entry.1.params =
              [{ name := "value", ty := CompilationModel.ParamType.uint256 }] :=
          hSourceParams entry hEntryMem hEntrySelector
        have hBodyStmts :
            bodyStmts =
              [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
                [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
              Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])] :=
          hSourceBody entry bodyStmts hEntryMem hEntrySelector hbody
        constructor
        · rw [hirFn]
          simp [Compiler.Proofs.IRGeneration.FunctionShape.compiledFunctionIR,
            hSpecParams, CompilationModel.Param.toIRParam,
            CompilationModel.ParamType.toIRType]
        · rw [hirFn]
          simp [Compiler.Proofs.IRGeneration.FunctionShape.compiledFunctionIR,
            hSpecParams, hBodyStmts]
      · have hFindTail :
            tailIr.find? (fun fn => fn.selector == tx.functionSelector) =
              some irFn := by
          simpa [hSelector] using hFind
        exact ih
          (fun entry' hMem =>
            hSourceParams entry' (by simp [hMem]))
          (fun entry' bodyStmts hMem =>
            hSourceBody entry' bodyStmts (by simp [hMem]))
          hFindTail

private theorem selectedGeneratedFunction_oneParam_store0_value_stop_shape_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSourceParams :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        entry.1.params =
          [{ name := "value", ty := CompilationModel.ParamType.uint256 }])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList spec.fields spec.events spec.errors
          .calldata [] false (entry.1.params.map (·.name)) []
          entry.1.body = Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (irFn : IRFunction)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some irFn) :
    irFn.params = [{ name := "value", ty := IRType.uint256 }] ∧
    irFn.body =
      Compiler.CompilationModel.genParamLoads
        [{ name := "value", ty := CompilationModel.ParamType.uint256 }] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])] := by
  have hcompiled :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hcompile
  exact
    selectedCompiledFunction_oneParam_store0_value_stop_shape_of_forall₂
      spec.fields spec.events spec.errors tx hcompiled hSourceParams
      hSourceBody irFn hFind

private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_source_oneParam_store0_value_stop
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (hSourceParams :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        entry.1.params =
          [{ name := "value", ty := CompilationModel.ParamType.uint256 }])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList spec.fields spec.events spec.errors
          .calldata [] false (entry.1.params.map (·.name)) []
          entry.1.body = Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_oneParam_store0_value_stop
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap hThreshold
      (fun fn hFind =>
        (selectedGeneratedFunction_oneParam_store0_value_stop_shape_of_compile_ok_supported
          spec selectors hSupported irContract tx hcompile hSourceParams
          hSourceBody fn hFind).1)
      (fun fn hFind =>
        (selectedGeneratedFunction_oneParam_store0_value_stop_shape_of_compile_ok_supported
          spec selectors hSupported irContract tx hcompile hSourceParams
          hSourceBody fn hFind).2)
      hArgsCons

private theorem compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher_source_oneParam_store0_value_stop
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSourceParams :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        entry.1.params =
          [{ name := "value", ty := CompilationModel.ParamType.uint256 }])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList spec.fields spec.events spec.errors
          .calldata [] false (entry.1.params.map (·.name)) []
          entry.1.body = Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])])
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      sourceResultMatchesNativeOn observableSlots
        (supportedSourceContractSemantics spec selectors hSupported tx
          initialWorld)
        (nativeGeneratedCallDispatcherResultOf irContract tx
          (FunctionBody.initialIRStateForTx spec tx initialWorld)
          observableSlots nativeContract) := by
  rcases
      nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_source_oneParam_store0_value_stop
        spec selectors hSupported irContract tx
        (FunctionBody.initialIRStateForTx spec tx initialWorld)
        observableSlots hcompile hSelectorRange hSelectorsRange hNoWrap
        (fun fn hFind =>
          generatedFunctionCalldataThreshold_of_compile_ok_supported
            spec selectors hSupported irContract tx hcompile fn hFind)
        hSourceParams hSourceBody hArgsCons with
    ⟨nativeContract, hLower, hMatch⟩
  exact
    ⟨nativeContract, hLower,
      compile_preserves_native_evmYulLean_of_nativeGeneratedCallDispatcherResult_match
        spec selectors hSupported irContract tx initialWorld observableSlots
        nativeContract htxNormalized hcalldataSizeFits hcompile hMatch⟩

/-- The direct lowered literal-return halt projects to the same observable
result as the selected IR body `mstore(0, value); return(0, 32)`. -/
private theorem nativeResultsMatchOn_execIRFunction_mstore0_lit_return32_markedPrefix
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (value : Nat)
    (hValueRange : value < EvmYul.UInt256.size)
    (hBody : fn.body = [
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    let yulTx := YulTransaction.ofIR tx
    let slots :=
      Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots
    let markedStore :=
      (((store.insert
        (Backends.nativeSwitchDiscrTempName switchId)
        (EvmYul.UInt256.ofNat
          (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1))
    let shared :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        nativeContract yulTx state.storage slots
    let shared1 : EvmYul.SharedState .Yul :=
      { shared with
        toMachineState :=
          shared.toMachineState.mstore
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat value) }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared2 markedStore) ⟨1⟩)))) := by
  intro yulTx slots markedStore shared shared1 shared2
  have hIR :=
    Compiler.Proofs.IRGeneration.execIRFunction_mstore0_lit_return32
      fn tx state value hBody
  have hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared2 markedStore) ⟨1⟩)) =
        { success := true,
          returnValue := some (EvmYul.UInt256.ofNat value).toNat,
          finalStorage :=
            Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              yulTx (EvmYul.Yul.State.Ok shared2 markedStore),
          finalMappings :=
            Compiler.Proofs.storageAsMappings
              (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
                yulTx (EvmYul.Yul.State.Ok shared2 markedStore)),
          events :=
            state.events ++
              Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
                (EvmYul.Yul.State.Ok shared2 markedStore) } := by
    have hMemorySize : 32 ≤ shared.memory.size := by
      simpa [shared] using
        nativeSwitchPostInitFreeMemorySharedState_memory_size_ge_32
          nativeContract yulTx state.storage slots
    simpa [yulTx, shared, shared1, shared2] using
      projectResult_literalReturnHit_eq yulTx state.storage state.events
        shared markedStore value hMemorySize
  have hValueNat : (EvmYul.UInt256.ofNat value).toNat = value := by
    have hValueRange' : value < Verity.Core.UINT256_MODULUS := by
      simpa [EvmYul.UInt256.size, Verity.Core.UINT256_MODULUS] using hValueRange
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt hValueRange']
    rfl
  have hLogs :
      Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
        (EvmYul.Yul.State.Ok shared2 markedStore) = [] := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
      shared2, shared1, shared,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.Yul.State.sharedState]
    rfl
  rw [hIR, hProject]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [hValueNat]
  · intro slot hslot
    have hslot' : slot ∈ slots := by
      simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
        hslot]
    have hAccountMap :
        shared2.accountMap =
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            nativeContract yulTx state.storage slots).sharedState.accountMap := by
      simpa [shared2, shared1, shared] using
        nativeSwitchPostInitFreeMemorySharedState_accountMap
          nativeContract yulTx state.storage slots
    have hNative :=
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_materializedStorageSlot
        nativeContract yulTx state.storage slots slot hslot'
    have hNative' :
        Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
          yulTx (EvmYul.Yul.State.Ok shared2 markedStore)
            (IRStorageSlot.ofNat slot) =
          state.storage (IRStorageSlot.ofNat slot) := by
      simpa [Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState,
        Compiler.Proofs.YulGeneration.Backends.StateBridge.extractStorage,
        EvmYul.Yul.State.sharedState, hAccountMap] using hNative
    exact hNative'.symm
  · rw [hLogs, List.append_nil]

/-- The lowered zero-parameter literal-return halt projects to the same
observable result as the generated IR body
`genParamLoads [] ++ [mstore(0, value); return(0, 32)]`. -/
private theorem nativeResultsMatchOn_execIRFunction_zeroParam_mstore0_lit_return32_markedPrefix
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (value : Nat)
    (hValueRange : value < EvmYul.UInt256.size)
    (hParams : fn.params = [])
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : fn.body =
      Compiler.CompilationModel.genParamLoads [] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    let yulTx := YulTransaction.ofIR tx
    let slots :=
      Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots
    let markedStore :=
      (((store.insert
        (Backends.nativeSwitchDiscrTempName switchId)
        (EvmYul.UInt256.ofNat
          (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1))
    let shared :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        nativeContract yulTx state.storage slots
    let shared1 : EvmYul.SharedState .Yul :=
      { shared with
        toMachineState :=
          shared.toMachineState.mstore
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat value) }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared2 markedStore) ⟨1⟩)))) := by
  intro yulTx slots markedStore shared shared1 shared2
  have hIR :=
    execIRFunction_zeroParam_mstore0_lit_return32
      fn tx state value hParams hNoWrap hBody
  have hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared2 markedStore) ⟨1⟩)) =
        { success := true,
          returnValue := some (EvmYul.UInt256.ofNat value).toNat,
          finalStorage :=
            Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              yulTx (EvmYul.Yul.State.Ok shared2 markedStore),
          finalMappings :=
            Compiler.Proofs.storageAsMappings
              (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
                yulTx (EvmYul.Yul.State.Ok shared2 markedStore)),
          events :=
            state.events ++
              Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
                (EvmYul.Yul.State.Ok shared2 markedStore) } := by
    have hMemorySize : 32 ≤ shared.memory.size := by
      simpa [shared] using
        nativeSwitchPostInitFreeMemorySharedState_memory_size_ge_32
          nativeContract yulTx state.storage slots
    simpa [yulTx, shared, shared1, shared2] using
      projectResult_literalReturnHit_eq yulTx state.storage state.events
        shared markedStore value hMemorySize
  have hValueNat : (EvmYul.UInt256.ofNat value).toNat = value := by
    have hValueRange' : value < Verity.Core.UINT256_MODULUS := by
      simpa [EvmYul.UInt256.size, Verity.Core.UINT256_MODULUS] using hValueRange
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt hValueRange']
    rfl
  have hLogs :
      Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
        (EvmYul.Yul.State.Ok shared2 markedStore) = [] := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
      shared2, shared1, shared,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.Yul.State.sharedState]
    rfl
  rw [hIR, hProject]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [hValueNat]
  · intro slot hslot
    have hslot' : slot ∈ slots := by
      simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
        hslot]
    have hAccountMap :
        shared2.accountMap =
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            nativeContract yulTx state.storage slots).sharedState.accountMap := by
      simpa [shared2, shared1, shared] using
        nativeSwitchPostInitFreeMemorySharedState_accountMap
          nativeContract yulTx state.storage slots
    have hNative :=
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_materializedStorageSlot
        nativeContract yulTx state.storage slots slot hslot'
    have hNative' :
        Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
          yulTx (EvmYul.Yul.State.Ok shared2 markedStore)
            (IRStorageSlot.ofNat slot) =
          state.storage (IRStorageSlot.ofNat slot) := by
      simpa [Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState,
        Compiler.Proofs.YulGeneration.Backends.StateBridge.extractStorage,
        EvmYul.Yul.State.sharedState, hAccountMap] using hNative
    exact hNative'.symm
  · rw [hLogs, List.append_nil]

/-- The lowered zero-parameter storage-return halt projects to the same
observable result as the generated IR body
`genParamLoads [] ++ [mstore(0, sload(0)); return(0, 32)]`. -/
private theorem nativeResultsMatchOn_execIRFunction_zeroParam_mstore0_sload0_return32_markedPrefix
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (hParams : fn.params = [])
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : fn.body =
      Compiler.CompilationModel.genParamLoads [] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    let yulTx := YulTransaction.ofIR tx
    let slots :=
      Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots
    let markedStore :=
      (((store.insert
        (Backends.nativeSwitchDiscrTempName switchId)
        (EvmYul.UInt256.ofNat
          (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1))
    let shared :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        nativeContract yulTx state.storage slots
    let p := shared.sload (EvmYul.UInt256.ofNat 0)
    let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
    let shared3 : EvmYul.SharedState .Yul :=
      { shared2 with
        toMachineState :=
          shared2.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared3 markedStore) ⟨1⟩)))) := by
  intro yulTx slots markedStore shared p shared1 shared2 shared3
  have hIR :=
    execIRFunction_zeroParam_mstore0_sload0_return32
      fn tx state hParams hNoWrap hBody
  have hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared3 markedStore) ⟨1⟩)) =
        { success := true,
          returnValue := some p.2.toNat,
          finalStorage :=
            Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              yulTx (EvmYul.Yul.State.Ok shared3 markedStore),
          finalMappings :=
            Compiler.Proofs.storageAsMappings
              (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
                yulTx (EvmYul.Yul.State.Ok shared3 markedStore)),
          events :=
            state.events ++
              Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
                (EvmYul.Yul.State.Ok shared3 markedStore) } := by
    have hMemorySize : 32 ≤ shared.memory.size := by
      simpa [shared] using
        nativeSwitchPostInitFreeMemorySharedState_memory_size_ge_32
          nativeContract yulTx state.storage slots
    simpa [yulTx, shared, p, shared1, shared2, shared3] using
      projectResult_retrieveHit_eq yulTx state.storage state.events
        shared markedStore hMemorySize
  have hSlotZero : 0 ∈ slots := by
    simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots]
  have hp :
      p.2 = state.storage (IRStorageSlot.ofNat 0) := by
    have hload :=
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_sload_materializedSlot_value
        nativeContract yulTx state.storage slots 0 hSlotZero
    have hsload := congrArg
      (fun s : EvmYul.State .Yul =>
        (s.sload (EvmYul.UInt256.ofNat 0)).2)
      (nativeSwitchPostInitFreeMemorySharedState_toState
        nativeContract yulTx state.storage slots)
    exact (by simpa [p, shared] using hsload.trans hload)
  have hLogs :
      Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
        (EvmYul.Yul.State.Ok shared3 markedStore) = [] := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
      shared3, shared2, shared1, p, shared,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.State.sload, EvmYul.State.addAccessedStorageKey,
      EvmYul.Substate.addAccessedStorageKey, EvmYul.Yul.State.sharedState]
    rfl
  rw [hIR, hProject]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [hp, Compiler.Proofs.IRGeneration.IRStorageWord.toNat]
  · intro slot hslot
    have hslot' : slot ∈ slots := by
      simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
        hslot]
    have hNative :=
      Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState_retrieveHit_initialState_materialized
        nativeContract yulTx state.storage slots markedStore slot hslot'
    exact hNative.symm
  · rw [hLogs, List.append_nil]

private theorem list_getD_eq_of_drop_eq_cons
    {xs : List Nat} {idx arg : Nat} {rest : List Nat}
    (hdrop : xs.drop idx = arg :: rest) :
    xs.getD idx 0 = arg := by
  have hlookup : xs[idx]? = some arg := by
    simpa [hdrop, Nat.zero_add] using
      (List.getElem?_drop (xs := xs) (i := idx) (j := 0)).symm
  simp [List.getD, hlookup]

/-- The direct lowered aligned-argument return halt projects to the same
observable result as the selected IR body
`mstore(0, calldataload(4 + 32*idx)); return(0, 32)`. -/
private theorem nativeResultsMatchOn_execIRFunction_mstore0_calldataload_aligned_return32_markedPrefix
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (idx arg : Nat) (rest : List Nat)
    (hdrop : tx.args.drop idx = arg :: rest)
    (hBody : fn.body = [
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0,
         Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit (4 + 32 * idx)]]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    let yulTx := YulTransaction.ofIR tx
    let slots :=
      Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots
    let markedStore :=
      (((store.insert
        (Backends.nativeSwitchDiscrTempName switchId)
        (EvmYul.UInt256.ofNat
          (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1))
    let shared :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        nativeContract yulTx state.storage slots
    let value := Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg
    let shared1 : EvmYul.SharedState .Yul :=
      { shared with
        toMachineState :=
          shared.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared2 markedStore) ⟨1⟩)))) := by
  intro yulTx slots markedStore shared value shared1 shared2
  have hIR :=
    Compiler.Proofs.IRGeneration.execIRFunction_mstore0_calldataload_aligned_return32
      fn tx state idx hBody
  have hGetD : tx.args.getD idx 0 = arg :=
    list_getD_eq_of_drop_eq_cons hdrop
  have hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared2 markedStore) ⟨1⟩)) =
        { success := true,
          returnValue := some value.toNat,
          finalStorage :=
            Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              yulTx (EvmYul.Yul.State.Ok shared2 markedStore),
          finalMappings :=
            Compiler.Proofs.storageAsMappings
              (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
                yulTx (EvmYul.Yul.State.Ok shared2 markedStore)),
          events :=
            state.events ++
              Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
                (EvmYul.Yul.State.Ok shared2 markedStore) } := by
    have hMemorySize : 32 ≤ shared.memory.size := by
      simpa [shared] using
        nativeSwitchPostInitFreeMemorySharedState_memory_size_ge_32
          nativeContract yulTx state.storage slots
    simpa [yulTx, shared, value, shared1, shared2,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256] using
      projectResult_literalReturnHit_eq yulTx state.storage state.events
        shared markedStore arg hMemorySize
  have hValueNat :
      value.toNat = arg % Compiler.Constants.evmModulus := by
    simp [value,
      EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat, Fin.ofNat,
      Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]
    rfl
  have hLogs :
      Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
        (EvmYul.Yul.State.Ok shared2 markedStore) = [] := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
      shared2, shared1, shared,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.Yul.State.sharedState]
    rfl
  rw [hIR, hGetD, hProject]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [hValueNat]
  · intro slot hslot
    have hslot' : slot ∈ slots := by
      simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
        hslot]
    have hAccountMap :
        shared2.accountMap =
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            nativeContract yulTx state.storage slots).sharedState.accountMap := by
      simpa [shared2, shared1, shared] using
        nativeSwitchPostInitFreeMemorySharedState_accountMap
          nativeContract yulTx state.storage slots
    have hNative :=
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_materializedStorageSlot
        nativeContract yulTx state.storage slots slot hslot'
    have hNative' :
        Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
          yulTx (EvmYul.Yul.State.Ok shared2 markedStore)
            (IRStorageSlot.ofNat slot) =
          state.storage (IRStorageSlot.ofNat slot) := by
      simpa [Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState,
        Compiler.Proofs.YulGeneration.Backends.StateBridge.extractStorage,
        EvmYul.Yul.State.sharedState, hAccountMap] using hNative
    exact hNative'.symm
  · rw [hLogs, List.append_nil]

/-- The direct lowered single-argument return halt projects to the same
observable result as the selected IR body
`mstore(0, calldataload(4)); return(0, 32)`. -/
private theorem nativeResultsMatchOn_execIRFunction_mstore0_calldataload4_return32_markedPrefix
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat) (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hBody : fn.body = [
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0,
         Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    let yulTx := YulTransaction.ofIR tx
    let slots :=
      Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots
    let markedStore :=
      (((store.insert
        (Backends.nativeSwitchDiscrTempName switchId)
        (EvmYul.UInt256.ofNat
          (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1))
    let shared :=
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        nativeContract yulTx state.storage slots
    let value := Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg
    let shared1 : EvmYul.SharedState .Yul :=
      { shared with
        toMachineState :=
          shared.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared2 markedStore) ⟨1⟩)))) := by
  intro yulTx slots markedStore shared value shared1 shared2
  have hIR :=
    Compiler.Proofs.IRGeneration.execIRFunction_mstore0_calldataload4_return32_of_args_cons
      fn tx state arg rest hBody hArgs
  have hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared2 markedStore) ⟨1⟩)) =
        { success := true,
          returnValue := some value.toNat,
          finalStorage :=
            Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              yulTx (EvmYul.Yul.State.Ok shared2 markedStore),
          finalMappings :=
            Compiler.Proofs.storageAsMappings
              (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
                yulTx (EvmYul.Yul.State.Ok shared2 markedStore)),
          events :=
            state.events ++
              Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
                (EvmYul.Yul.State.Ok shared2 markedStore) } := by
    have hMemorySize : 32 ≤ shared.memory.size := by
      simpa [shared] using
        nativeSwitchPostInitFreeMemorySharedState_memory_size_ge_32
          nativeContract yulTx state.storage slots
    simpa [yulTx, shared, value, shared1, shared2,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256] using
      projectResult_literalReturnHit_eq yulTx state.storage state.events
        shared markedStore arg hMemorySize
  have hValueNat :
      value.toNat = arg % Compiler.Constants.evmModulus := by
    simp [value,
      EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat, Fin.ofNat,
      Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]
    rfl
  have hLogs :
      Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
        (EvmYul.Yul.State.Ok shared2 markedStore) = [] := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
      shared2, shared1, shared,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.Yul.State.sharedState]
    rfl
  rw [hIR, hProject]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [hValueNat]
  · intro slot hslot
    have hslot' : slot ∈ slots := by
      simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
        hslot]
    have hAccountMap :
        shared2.accountMap =
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            nativeContract yulTx state.storage slots).sharedState.accountMap := by
      simpa [shared2, shared1, shared] using
        nativeSwitchPostInitFreeMemorySharedState_accountMap
          nativeContract yulTx state.storage slots
    have hNative :=
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_materializedStorageSlot
        nativeContract yulTx state.storage slots slot hslot'
    have hNative' :
        Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
          yulTx (EvmYul.Yul.State.Ok shared2 markedStore)
            (IRStorageSlot.ofNat slot) =
          state.storage (IRStorageSlot.ofNat slot) := by
      simpa [Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState,
        Compiler.Proofs.YulGeneration.Backends.StateBridge.extractStorage,
        EvmYul.Yul.State.sharedState, hAccountMap] using hNative
    exact hNative'.symm
  · rw [hLogs, List.append_nil]

/-- Build the direct selected-user-body halt bridge for the generated
`retrieve()` body shape. -/
private theorem NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_mstore0_sload0_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hRetrieveBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state
      observableSlots := by
  intro nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
    userBodyStart _hLowerRuntime hFind hUserBodyLower _hguards _hArgs
  have hBody := hRetrieveBody fn hFind
  have hLowerConcrete :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames userBodyStart
          ([Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
            Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
              [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] : List Yul.YulStmt) =
        .ok (simpleStorageLoweredRetrieveCaseBodyTail3, userBodyStart) := by
    simp [simpleStorageLoweredRetrieveCaseBodyTail3,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_expr,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
  have hLowerPair :
      (bodyNative, bodyEnd) = (simpleStorageLoweredRetrieveCaseBodyTail3, userBodyStart) := by
    rw [hBody, hLowerConcrete] at hUserBodyLower
    simpa using hUserBodyLower.symm
  rcases hLowerPair with ⟨rfl, rfl⟩
  let switchId :=
    Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode irContract) observableSlots
  let markedStore :=
    (((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore.insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1))
  let shared :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      nativeContract yulTx state.storage slots
  let p := shared.sload (EvmYul.UInt256.ofNat 0)
  let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
  let shared2 : EvmYul.SharedState .Yul :=
    { shared1 with
      toMachineState :=
        shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
  let shared3 : EvmYul.SharedState .Yul :=
    { shared2 with
      toMachineState :=
        shared2.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
  let haltState := EvmYul.Yul.State.Ok shared3 markedStore
  let nativeYul :=
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      yulTx state.storage state.events
      (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨1⟩))
  refine ⟨haltState, ⟨1⟩, nativeYul, ?_, rfl, ?_⟩
  · intro _pre suffix
    have hExec :=
      exec_block_simpleStorageLoweredRetrieveCaseBodyTail3_closed
        (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
          suffix.length + 1)
        (some nativeContract) shared markedStore
    change
      EvmYul.Yul.exec
          (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
              suffix.length + 10)
          (.Block simpleStorageLoweredRetrieveCaseBodyTail3)
          (some nativeContract) (EvmYul.Yul.State.Ok shared markedStore) =
        .error (EvmYul.Yul.Exception.YulHalt haltState ⟨1⟩)
    rw [show
        nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
            suffix.length + 10 =
          nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
            suffix.length + 1 + 9 by
        rw [show (10 : Nat) = 1 + 9 by rfl]]
    simpa [switchId, yulTx, slots, markedStore, shared, p, shared1, shared2, shared3, haltState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.Yul.State.sharedState] using hExec
  · simpa [switchId, yulTx, slots, markedStore, shared, p, shared1, shared2,
      shared3, haltState, nativeYul] using
      (nativeResultsMatchOn_execIRFunction_mstore0_sload0_return32_markedPrefix
        irContract tx state observableSlots nativeContract fn switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
        hBody)

private theorem NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_zeroParam_mstore0_sload0_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hParams :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.params = [])
    (hRetrieveBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body =
          Compiler.CompilationModel.genParamLoads [] ++
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state
      observableSlots := by
  intro nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
    userBodyStart _hLowerRuntime hFind hUserBodyLower _hguards _hArgs
  have hBody := hRetrieveBody fn hFind
  have hFnParams := hParams fn hFind
  have hLowerConcrete :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames userBodyStart
          (Compiler.CompilationModel.genParamLoads [] ++
            [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
            Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
              [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] : List Yul.YulStmt) =
        .ok (loweredZeroParamSload0ReturnCaseBody, userBodyStart) := by
    simp [loweredZeroParamSload0ReturnCaseBody,
      simpleStorageLoweredRetrieveCaseBodyTail3,
      Compiler.CompilationModel.genParamLoads,
      Compiler.CompilationModel.genParamLoadsFrom,
      Compiler.CompilationModel.genParamLoadBodyFrom,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_expr,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_if,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
  have hLowerPair :
      (bodyNative, bodyEnd) =
        (loweredZeroParamSload0ReturnCaseBody, userBodyStart) := by
    rw [hBody, hLowerConcrete] at hUserBodyLower
    simpa using hUserBodyLower.symm
  rcases hLowerPair with ⟨rfl, rfl⟩
  let switchId :=
    Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode irContract) observableSlots
  let markedStore :=
    (((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore.insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1))
  let shared :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      nativeContract yulTx state.storage slots
  let p := shared.sload (EvmYul.UInt256.ofNat 0)
  let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
  let shared2 : EvmYul.SharedState .Yul :=
    { shared1 with
      toMachineState :=
        shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
  let shared3 : EvmYul.SharedState .Yul :=
    { shared2 with
      toMachineState :=
        shared2.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
  let haltState := EvmYul.Yul.State.Ok shared3 markedStore
  let nativeYul :=
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      yulTx state.storage state.events
      (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨1⟩))
  refine ⟨haltState, ⟨1⟩, nativeYul, ?_, rfl, ?_⟩
  · intro _pre suffix
    have hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size := by
      rw [show shared.executionEnv.calldata.size =
          4 + yulTx.args.length * 32 by
        simpa [shared] using
          nativeSwitchPostInitFreeMemorySharedState_calldata_size
            nativeContract yulTx state.storage slots]
      simpa [yulTx, YulTransaction.ofIR_args] using hNoWrap
    have hGe : 4 ≤ shared.executionEnv.calldata.size := by
      rw [show shared.executionEnv.calldata.size =
          4 + yulTx.args.length * 32 by
        simpa [shared] using
          nativeSwitchPostInitFreeMemorySharedState_calldata_size
            nativeContract yulTx state.storage slots]
      exact Nat.le_add_right 4 _
    have hExec :=
      exec_block_loweredZeroParamSload0ReturnCaseBody_closed
        (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
          suffix.length)
        (some nativeContract) shared markedStore hSize hGe
    change EvmYul.Yul.exec _ _ _ (EvmYul.Yul.State.Ok shared markedStore) = _
    simpa [switchId, yulTx, slots, markedStore, shared, p, shared1, shared2, shared3,
      haltState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState] using hExec
  · simpa [switchId, yulTx, slots, markedStore, shared, p, shared1, shared2,
      shared3, haltState, nativeYul] using
      (nativeResultsMatchOn_execIRFunction_zeroParam_mstore0_sload0_return32_markedPrefix
        irContract tx state observableSlots nativeContract fn switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
        hFnParams hNoWrap hBody)

private theorem NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_mstore0_lit_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (value : Nat)
    (hValueRange : value < EvmYul.UInt256.size)
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state
      observableSlots := by
  intro nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
    userBodyStart _hLowerRuntime hFind hUserBodyLower _hguards _hArgs
  have hBody := hReturnBody fn hFind
  have hLowerConcrete :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames userBodyStart
          ([Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
            Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
              [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] : List Yul.YulStmt) =
        .ok (loweredLiteralReturnCaseBodyTail value, userBodyStart) := by
    simp [loweredLiteralReturnCaseBodyTail,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_expr,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
  have hLowerPair :
      (bodyNative, bodyEnd) = (loweredLiteralReturnCaseBodyTail value, userBodyStart) := by
    rw [hBody, hLowerConcrete] at hUserBodyLower
    simpa using hUserBodyLower.symm
  rcases hLowerPair with ⟨rfl, rfl⟩
  let switchId :=
    Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode irContract) observableSlots
  let markedStore :=
    (((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore.insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1))
  let shared :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      nativeContract yulTx state.storage slots
  let shared1 : EvmYul.SharedState .Yul :=
    { shared with
      toMachineState :=
        shared.toMachineState.mstore
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat value) }
  let shared2 : EvmYul.SharedState .Yul :=
    { shared1 with
      toMachineState :=
        shared1.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
  let haltState := EvmYul.Yul.State.Ok shared2 markedStore
  let nativeYul :=
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      yulTx state.storage state.events
      (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨1⟩))
  refine ⟨haltState, ⟨1⟩, nativeYul, ?_, rfl, ?_⟩
  · intro _pre suffix
    have hExec :=
      exec_block_loweredLiteralReturnCaseBodyTail_closed
        (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
          suffix.length + 2)
        (some nativeContract) shared markedStore value
    rw [show
        nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
            suffix.length + 10 =
          nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
            suffix.length + 2 + 8 by
        rw [show (10 : Nat) = 2 + 8 by rfl]]
    change EvmYul.Yul.exec _ _ _ (EvmYul.Yul.State.Ok shared markedStore) = _
    simpa [switchId, yulTx, slots, markedStore, shared, shared1, shared2, haltState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState] using hExec
  · simpa [switchId, yulTx, slots, markedStore, shared, shared1, shared2,
      haltState, nativeYul] using
      (nativeResultsMatchOn_execIRFunction_mstore0_lit_return32_markedPrefix
        irContract tx state observableSlots nativeContract fn switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
        value hValueRange hBody)

private theorem NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_zeroParam_mstore0_lit_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (value : Nat)
    (hValueRange : value < EvmYul.UInt256.size)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hParams :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.params = [])
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body =
          Compiler.CompilationModel.genParamLoads [] ++
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state
      observableSlots := by
  intro nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
    userBodyStart _hLowerRuntime hFind hUserBodyLower _hguards _hArgs
  have hBody := hReturnBody fn hFind
  have hFnParams := hParams fn hFind
  have hLowerConcrete :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames userBodyStart
          (Compiler.CompilationModel.genParamLoads [] ++
            [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
            Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
              [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] : List Yul.YulStmt) =
        .ok (loweredZeroParamLiteralReturnCaseBody value, userBodyStart) := by
    simp [loweredZeroParamLiteralReturnCaseBody, loweredLiteralReturnCaseBodyTail,
      Compiler.CompilationModel.genParamLoads,
      Compiler.CompilationModel.genParamLoadsFrom,
      Compiler.CompilationModel.genParamLoadBodyFrom,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_expr,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_if,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
  have hLowerPair :
      (bodyNative, bodyEnd) =
        (loweredZeroParamLiteralReturnCaseBody value, userBodyStart) := by
    rw [hBody, hLowerConcrete] at hUserBodyLower
    simpa using hUserBodyLower.symm
  rcases hLowerPair with ⟨rfl, rfl⟩
  let switchId :=
    Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode irContract) observableSlots
  let markedStore :=
    (((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore.insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1))
  let shared :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      nativeContract yulTx state.storage slots
  let shared1 : EvmYul.SharedState .Yul :=
    { shared with
      toMachineState :=
        shared.toMachineState.mstore
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat value) }
  let shared2 : EvmYul.SharedState .Yul :=
    { shared1 with
      toMachineState :=
        shared1.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
  let haltState := EvmYul.Yul.State.Ok shared2 markedStore
  let nativeYul :=
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      yulTx state.storage state.events
      (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨1⟩))
  refine ⟨haltState, ⟨1⟩, nativeYul, ?_, rfl, ?_⟩
  · intro _pre suffix
    have hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size := by
      rw [show shared.executionEnv.calldata.size =
          4 + yulTx.args.length * 32 by
        simpa [shared] using
          nativeSwitchPostInitFreeMemorySharedState_calldata_size
            nativeContract yulTx state.storage slots]
      simpa [yulTx, YulTransaction.ofIR_args] using hNoWrap
    have hGe : 4 ≤ shared.executionEnv.calldata.size := by
      rw [show shared.executionEnv.calldata.size =
          4 + yulTx.args.length * 32 by
        simpa [shared] using
          nativeSwitchPostInitFreeMemorySharedState_calldata_size
            nativeContract yulTx state.storage slots]
      exact Nat.le_add_right 4 _
    have hExec :=
      exec_block_loweredZeroParamLiteralReturnCaseBody_closed
        (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
          suffix.length)
        (some nativeContract) shared markedStore value hSize hGe
    change EvmYul.Yul.exec _ _ _ (EvmYul.Yul.State.Ok shared markedStore) = _
    simpa [switchId, yulTx, slots, markedStore, shared, shared1, shared2, haltState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState] using hExec
  · simpa [switchId, yulTx, slots, markedStore, shared, shared1, shared2,
      haltState, nativeYul] using
      (nativeResultsMatchOn_execIRFunction_zeroParam_mstore0_lit_return32_markedPrefix
        irContract tx state observableSlots nativeContract fn switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
        value hValueRange hFnParams hNoWrap hBody)

private theorem NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_mstore0_calldataload4_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest)
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state
      observableSlots := by
  rcases hArgsCons with ⟨arg, rest, hArgs⟩
  intro nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
    userBodyStart _hLowerRuntime hFind hUserBodyLower _hguards _hArgs
  have hBody := hReturnBody fn hFind
  have hLowerConcrete :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames userBodyStart
          ([Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit 0,
               Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]]),
            Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
              [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] : List Yul.YulStmt) =
        .ok (loweredCalldataload4ReturnCaseBodyTail, userBodyStart) := by
    simp [loweredCalldataload4ReturnCaseBodyTail,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_expr,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
  have hLowerPair :
      (bodyNative, bodyEnd) = (loweredCalldataload4ReturnCaseBodyTail, userBodyStart) := by
    rw [hBody, hLowerConcrete] at hUserBodyLower
    simpa using hUserBodyLower.symm
  rcases hLowerPair with ⟨rfl, rfl⟩
  let switchId :=
    Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode irContract) observableSlots
  let markedStore :=
    (((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore.insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1))
  let shared :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      nativeContract yulTx state.storage slots
  let value := Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg
  let shared1 : EvmYul.SharedState .Yul :=
    { shared with
      toMachineState :=
        shared.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
  let shared2 : EvmYul.SharedState .Yul :=
    { shared1 with
      toMachineState :=
        shared1.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
  let haltState := EvmYul.Yul.State.Ok shared2 markedStore
  let nativeYul :=
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      yulTx state.storage state.events
      (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨1⟩))
  refine ⟨haltState, ⟨1⟩, nativeYul, ?_, rfl, ?_⟩
  · intro _pre suffix
    have hWord :
        shared.calldataload (EvmYul.UInt256.ofNat 4) = value := by
      simpa [shared, value,
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
        EvmYul.SharedState.toState,
        Compiler.Proofs.YulGeneration.Backends.Native.initialState,
        EvmYul.Yul.State.sharedState,
        EvmYul.Yul.State.toState] using
        Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataload4_arg0_word
          nativeContract yulTx state.storage slots arg rest hArgs
    have hExec :=
      exec_block_loweredCalldataload4ReturnCaseBodyTail_closed
        (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
          suffix.length + 1)
        (some nativeContract) shared markedStore arg hWord
    rw [show
        nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
            suffix.length + 10 =
          nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
            suffix.length + 1 + 9 by
        rw [show (10 : Nat) = 1 + 9 by rfl]]
    change EvmYul.Yul.exec _ _ _ (EvmYul.Yul.State.Ok shared markedStore) = _
    simpa [switchId, yulTx, slots, markedStore, shared, value, shared1, shared2,
      haltState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState] using hExec
  · simpa [switchId, yulTx, slots, markedStore, shared, value, shared1, shared2,
      haltState, nativeYul] using
      (nativeResultsMatchOn_execIRFunction_mstore0_calldataload4_return32_markedPrefix
        irContract tx state observableSlots nativeContract fn switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
        arg rest hArgs hBody)

private theorem NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_mstore0_calldataload_aligned_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (idx arg : Nat)
    (rest : List Nat)
    (hArgDrop : tx.args.drop idx = arg :: rest)
    (hOffset64 : 4 + 32 * idx < 2 ^ 64)
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit (4 + 32 * idx)]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state
      observableSlots := by
  intro nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
    userBodyStart _hLowerRuntime hFind hUserBodyLower _hguards _hArgs
  have hBody := hReturnBody fn hFind
  have hLowerConcrete :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames userBodyStart
          ([Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit 0,
               Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit (4 + 32 * idx)]]),
            Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
              [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] : List Yul.YulStmt) =
        .ok (loweredCalldataloadReturnCaseBodyTail idx, userBodyStart) := by
    simp [loweredCalldataloadReturnCaseBodyTail,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_expr,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
  have hLowerPair :
      (bodyNative, bodyEnd) =
        (loweredCalldataloadReturnCaseBodyTail idx, userBodyStart) := by
    rw [hBody, hLowerConcrete] at hUserBodyLower
    simpa using hUserBodyLower.symm
  rcases hLowerPair with ⟨rfl, rfl⟩
  let switchId :=
    Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode irContract) observableSlots
  let markedStore :=
    (((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore.insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (yulTx.functionSelector % Compiler.Constants.selectorModulus))).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1))
  let shared :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      nativeContract yulTx state.storage slots
  let value := Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg
  let shared1 : EvmYul.SharedState .Yul :=
    { shared with
      toMachineState :=
        shared.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
  let shared2 : EvmYul.SharedState .Yul :=
    { shared1 with
      toMachineState :=
        shared1.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
  let haltState := EvmYul.Yul.State.Ok shared2 markedStore
  let nativeYul :=
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      yulTx state.storage state.events
      (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨1⟩))
  refine ⟨haltState, ⟨1⟩, nativeYul, ?_, rfl, ?_⟩
  · intro _pre suffix
    have hWord :
        shared.calldataload (EvmYul.UInt256.ofNat (4 + 32 * idx)) = value := by
      simpa [shared, value, yulTx,
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
        EvmYul.SharedState.toState,
        Compiler.Proofs.YulGeneration.Backends.Native.initialState,
        EvmYul.Yul.State.sharedState,
        EvmYul.Yul.State.toState] using
        Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataload_aligned_arg_word
          nativeContract yulTx state.storage slots idx arg rest hArgDrop hOffset64
    have hExec :=
      exec_block_loweredCalldataloadReturnCaseBodyTail_closed
        (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
          suffix.length + 1)
        (some nativeContract) shared markedStore idx arg hWord
    rw [show
        nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
            suffix.length + 10 =
          nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
            suffix.length + 1 + 9 by
        rw [show (10 : Nat) = 1 + 9 by rfl]]
    change EvmYul.Yul.exec _ _ _ (EvmYul.Yul.State.Ok shared markedStore) = _
    simpa [switchId, yulTx, slots, markedStore, shared, value, shared1, shared2,
      haltState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState] using hExec
  · simpa [switchId, yulTx, slots, markedStore, shared, value, shared1, shared2,
      haltState, nativeYul] using
      (nativeResultsMatchOn_execIRFunction_mstore0_calldataload_aligned_return32_markedPrefix
        irContract tx state observableSlots nativeContract fn switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
        idx arg rest hArgDrop hBody)

private theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_mstore0_sload0_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hRetrieveBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_halt irContract tx state
    observableSlots
    (NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_mstore0_sload0_return32
      irContract tx state observableSlots hRetrieveBody)

private theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_zeroParam_mstore0_sload0_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hParams :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.params = [])
    (hRetrieveBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body =
          Compiler.CompilationModel.genParamLoads [] ++
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_halt irContract tx state
    observableSlots
    (NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_zeroParam_mstore0_sload0_return32
      irContract tx state observableSlots hNoWrap hParams hRetrieveBody)

private theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_mstore0_lit_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (value : Nat)
    (hValueRange : value < EvmYul.UInt256.size)
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_halt irContract tx state
    observableSlots
    (NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_mstore0_lit_return32
      irContract tx state observableSlots value hValueRange hReturnBody)

private theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_zeroParam_mstore0_lit_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (value : Nat)
    (hValueRange : value < EvmYul.UInt256.size)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hParams :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.params = [])
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body =
          Compiler.CompilationModel.genParamLoads [] ++
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_halt irContract tx state
    observableSlots
    (NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_zeroParam_mstore0_lit_return32
      irContract tx state observableSlots value hValueRange hNoWrap
      hParams hReturnBody)

private theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_mstore0_calldataload4_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest)
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_halt irContract tx state
    observableSlots
    (NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_mstore0_calldataload4_return32
      irContract tx state observableSlots hArgsCons hReturnBody)

private theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_mstore0_calldataload_aligned_return32
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (idx arg : Nat)
    (rest : List Nat)
    (hArgDrop : tx.args.drop idx = arg :: rest)
    (hOffset64 : 4 + 32 * idx < 2 ^ 64)
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit (4 + 32 * idx)]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_halt irContract tx state
    observableSlots
    (NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_mstore0_calldataload_aligned_return32
      irContract tx state observableSlots idx arg rest hArgDrop hOffset64 hReturnBody)

/-- Closed generated `callDispatcher` theorem for selected retrieve-body success.

This mirrors the store-body closed theorem through the unified selected-body
result boundary, discharging the selected user-body halt bridge from the
concrete native `mstore(0, sload(0)); return(0, 32)` proof above. -/
private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_mstore0_sload0_return32
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (hRetrieveBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap
      (NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_mstore0_sload0_return32
        irContract tx state observableSlots hRetrieveBody)
      hThreshold

/-- Closed generated `callDispatcher` theorem for a selected generated
zero-parameter storage-return body. The body includes `genParamLoads []`
before `mstore(0, sload(0)); return(0, 32)`. -/
private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_zeroParam_mstore0_sload0_return32
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (hParams :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.params = [])
    (hRetrieveBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body =
          Compiler.CompilationModel.genParamLoads [] ++
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap
      (NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_zeroParam_mstore0_sload0_return32
        irContract tx state observableSlots hNoWrap hParams hRetrieveBody)
      hThreshold

/-- Closed generated `callDispatcher` theorem for a selected literal-return
body `mstore(0, value); return(0, 32)`. -/
private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_mstore0_lit_return32
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (value : Nat)
    (hValueRange : value < EvmYul.UInt256.size)
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap
      (NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_mstore0_lit_return32
        irContract tx state observableSlots value hValueRange hReturnBody)
      hThreshold

private theorem selectedCompiledFunction_zeroParam_lit_return32_shape_of_forall₂
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef)
    (tx : IRTransaction)
    (value : Nat)
    {pairs : List (CompilationModel.FunctionSpec × Nat)}
    {irFns : List IRFunction}
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          CompilationModel.compileFunctionSpec fields events errors
            [] entry.2 entry.1 = Except.ok irFn)
        pairs irFns)
    (hSourceParams :
      ∀ entry, entry ∈ pairs → entry.2 = tx.functionSelector →
        entry.1.params = [])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ pairs →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList fields events errors .calldata
          [] false (entry.1.params.map (·.name)) [] entry.1.body =
            Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])])
    (irFn : IRFunction)
    (hFind :
      irFns.find? (fun fn => fn.selector == tx.functionSelector) =
        some irFn) :
    irFn.params = [] ∧
    irFn.body =
      Compiler.CompilationModel.genParamLoads [] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] := by
  induction hcompiled with
  | nil =>
      simp at hFind
  | @cons entry headIr tailPairs tailIr hhead htail ih =>
      by_cases hSelector : headIr.selector = tx.functionSelector
      · simp [hSelector] at hFind
        rcases hFind with rfl
        have hEntrySelector : entry.2 = tx.functionSelector := by
          have hSel :=
            Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_selector
              fields events errors entry.2 entry.1 headIr hhead
          simpa [hSelector] using hSel.symm
        rcases
            Compiler.Proofs.IRGeneration.FunctionShape.compileFunctionSpec_ok_components
              fields events errors entry.2 entry.1 headIr hhead with
          ⟨returns, bodyStmts, _hvalidate, _hreturns, hbody, hirFn⟩
        have hEntryMem : entry ∈ entry :: tailPairs := by simp
        have hSpecParams : entry.1.params = [] :=
          hSourceParams entry hEntryMem hEntrySelector
        have hBodyStmts :
            bodyStmts =
              [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
                [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
              Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
                [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] :=
          hSourceBody entry bodyStmts hEntryMem hEntrySelector hbody
        constructor
        · rw [hirFn]
          simp [Compiler.Proofs.IRGeneration.FunctionShape.compiledFunctionIR,
            hSpecParams]
        · rw [hirFn]
          simp [Compiler.Proofs.IRGeneration.FunctionShape.compiledFunctionIR,
            hSpecParams, hBodyStmts]
      · have hFindTail :
            tailIr.find? (fun fn => fn.selector == tx.functionSelector) =
              some irFn := by
          simpa [hSelector] using hFind
        exact ih
          (fun entry' hMem =>
            hSourceParams entry' (by simp [hMem]))
          (fun entry' bodyStmts hMem =>
            hSourceBody entry' bodyStmts (by simp [hMem]))
          hFindTail

private theorem selectedGeneratedFunction_zeroParam_lit_return32_shape_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (value : Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSourceParams :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        entry.1.params = [])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList spec.fields spec.events spec.errors
          .calldata [] false (entry.1.params.map (·.name)) []
          entry.1.body = Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])])
    (irFn : IRFunction)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some irFn) :
    irFn.params = [] ∧
    irFn.body =
      Compiler.CompilationModel.genParamLoads [] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] := by
  have hcompiled :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hcompile
  exact
    selectedCompiledFunction_zeroParam_lit_return32_shape_of_forall₂
      spec.fields spec.events spec.errors tx value hcompiled hSourceParams
      hSourceBody irFn hFind

private theorem selectedCompiledFunction_zeroParam_sload0_return32_shape_of_forall₂
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef)
    (tx : IRTransaction)
    {pairs : List (CompilationModel.FunctionSpec × Nat)}
    {irFns : List IRFunction}
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          CompilationModel.compileFunctionSpec fields events errors
            [] entry.2 entry.1 = Except.ok irFn)
        pairs irFns)
    (hSourceParams :
      ∀ entry, entry ∈ pairs → entry.2 = tx.functionSelector →
        entry.1.params = [])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ pairs →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList fields events errors .calldata
          [] false (entry.1.params.map (·.name)) [] entry.1.body =
            Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])])
    (irFn : IRFunction)
    (hFind :
      irFns.find? (fun fn => fn.selector == tx.functionSelector) =
        some irFn) :
    irFn.params = [] ∧
    irFn.body =
      Compiler.CompilationModel.genParamLoads [] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] := by
  induction hcompiled with
  | nil =>
      simp at hFind
  | @cons entry headIr tailPairs tailIr hhead htail ih =>
      by_cases hSelector : headIr.selector = tx.functionSelector
      · simp [hSelector] at hFind
        rcases hFind with rfl
        have hEntrySelector : entry.2 = tx.functionSelector := by
          have hSel :=
            Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_selector
              fields events errors entry.2 entry.1 headIr hhead
          simpa [hSelector] using hSel.symm
        rcases
            Compiler.Proofs.IRGeneration.FunctionShape.compileFunctionSpec_ok_components
              fields events errors entry.2 entry.1 headIr hhead with
          ⟨returns, bodyStmts, _hvalidate, _hreturns, hbody, hirFn⟩
        have hEntryMem : entry ∈ entry :: tailPairs := by simp
        have hSpecParams : entry.1.params = [] :=
          hSourceParams entry hEntryMem hEntrySelector
        have hBodyStmts :
            bodyStmts =
              [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
                [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
              Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
                [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] :=
          hSourceBody entry bodyStmts hEntryMem hEntrySelector hbody
        constructor
        · rw [hirFn]
          simp [Compiler.Proofs.IRGeneration.FunctionShape.compiledFunctionIR,
            hSpecParams]
        · rw [hirFn]
          simp [Compiler.Proofs.IRGeneration.FunctionShape.compiledFunctionIR,
            hSpecParams, hBodyStmts]
      · have hFindTail :
            tailIr.find? (fun fn => fn.selector == tx.functionSelector) =
              some irFn := by
          simpa [hSelector] using hFind
        exact ih
          (fun entry' hMem =>
            hSourceParams entry' (by simp [hMem]))
          (fun entry' bodyStmts hMem =>
            hSourceBody entry' bodyStmts (by simp [hMem]))
          hFindTail

private theorem selectedGeneratedFunction_zeroParam_sload0_return32_shape_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSourceParams :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        entry.1.params = [])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList spec.fields spec.events spec.errors
          .calldata [] false (entry.1.params.map (·.name)) []
          entry.1.body = Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])])
    (irFn : IRFunction)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some irFn) :
    irFn.params = [] ∧
    irFn.body =
      Compiler.CompilationModel.genParamLoads [] ++
      [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
      Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
        [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] := by
  have hcompiled :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hcompile
  exact
    selectedCompiledFunction_zeroParam_sload0_return32_shape_of_forall₂
      spec.fields spec.events spec.errors tx hcompiled hSourceParams
      hSourceBody irFn hFind

/-- Closed generated `callDispatcher` theorem for a selected generated
zero-parameter literal-return body. The body includes `genParamLoads []`
before `mstore(0, value); return(0, 32)`. -/
private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_zeroParam_mstore0_lit_return32
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (value : Nat)
    (hValueRange : value < EvmYul.UInt256.size)
    (hParams :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.params = [])
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body =
          Compiler.CompilationModel.genParamLoads [] ++
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap
      (NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_zeroParam_mstore0_lit_return32
        irContract tx state observableSlots value hValueRange hNoWrap
        hParams hReturnBody)
      hThreshold

/-- Source-shape variant of the closed generated `callDispatcher` theorem for
zero-parameter literal-return bodies. It derives the selected IR function
params/body shape from `compileFunctionSpec` instead of requiring direct
premises over `irContract.functions.find?`. -/
private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_source_zeroParam_lit_return32
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (value : Nat)
    (hValueRange : value < EvmYul.UInt256.size)
    (hSourceParams :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        entry.1.params = [])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList spec.fields spec.events spec.errors
          .calldata [] false (entry.1.params.map (·.name)) []
          entry.1.body = Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_zeroParam_mstore0_lit_return32
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap hThreshold value hValueRange
      (fun fn hFind =>
        (selectedGeneratedFunction_zeroParam_lit_return32_shape_of_compile_ok_supported
          spec selectors hSupported irContract tx value hcompile hSourceParams
          hSourceBody fn hFind).1)
      (fun fn hFind =>
        (selectedGeneratedFunction_zeroParam_lit_return32_shape_of_compile_ok_supported
          spec selectors hSupported irContract tx value hcompile hSourceParams
          hSourceBody fn hFind).2)

private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_source_zeroParam_sload0_return32
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (hSourceParams :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        entry.1.params = [])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList spec.fields spec.events spec.errors
          .calldata [] false (entry.1.params.map (·.name)) []
          entry.1.body = Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_zeroParam_mstore0_sload0_return32
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap hThreshold
      (fun fn hFind =>
        (selectedGeneratedFunction_zeroParam_sload0_return32_shape_of_compile_ok_supported
          spec selectors hSupported irContract tx hcompile hSourceParams
          hSourceBody fn hFind).1)
      (fun fn hFind =>
        (selectedGeneratedFunction_zeroParam_sload0_return32_shape_of_compile_ok_supported
          spec selectors hSupported irContract tx hcompile hSourceParams
          hSourceBody fn hFind).2)

private theorem compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher_source_zeroParam_lit_return32
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (value : Nat)
    (hValueRange : value < EvmYul.UInt256.size)
    (hSourceParams :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        entry.1.params = [])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList spec.fields spec.events spec.errors
          .calldata [] false (entry.1.params.map (·.name)) []
          entry.1.body = Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit value]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      sourceResultMatchesNativeOn observableSlots
        (supportedSourceContractSemantics spec selectors hSupported tx
          initialWorld)
        (nativeGeneratedCallDispatcherResultOf irContract tx
          (FunctionBody.initialIRStateForTx spec tx initialWorld)
          observableSlots nativeContract) := by
  rcases
      nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_source_zeroParam_lit_return32
        spec selectors hSupported irContract tx
        (FunctionBody.initialIRStateForTx spec tx initialWorld)
        observableSlots hcompile hSelectorRange hSelectorsRange hNoWrap
        (fun fn hFind =>
          generatedFunctionCalldataThreshold_of_compile_ok_supported
            spec selectors hSupported irContract tx hcompile fn hFind)
        value hValueRange hSourceParams hSourceBody with
    ⟨nativeContract, hLower, hMatch⟩
  exact
    ⟨nativeContract, hLower,
      compile_preserves_native_evmYulLean_of_nativeGeneratedCallDispatcherResult_match
        spec selectors hSupported irContract tx initialWorld observableSlots
        nativeContract htxNormalized hcalldataSizeFits hcompile hMatch⟩

private theorem compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher_source_zeroParam_sload0_return32
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSourceParams :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        entry.1.params = [])
    (hSourceBody :
      ∀ entry bodyStmts,
        entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        entry.2 = tx.functionSelector →
        CompilationModel.compileStmtList spec.fields spec.events spec.errors
          .calldata [] false (entry.1.params.map (·.name)) []
          entry.1.body = Except.ok bodyStmts →
        bodyStmts =
          [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      sourceResultMatchesNativeOn observableSlots
        (supportedSourceContractSemantics spec selectors hSupported tx
          initialWorld)
        (nativeGeneratedCallDispatcherResultOf irContract tx
          (FunctionBody.initialIRStateForTx spec tx initialWorld)
          observableSlots nativeContract) := by
  rcases
      nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_source_zeroParam_sload0_return32
        spec selectors hSupported irContract tx
        (FunctionBody.initialIRStateForTx spec tx initialWorld)
        observableSlots hcompile hSelectorRange hSelectorsRange hNoWrap
        (fun fn hFind =>
          generatedFunctionCalldataThreshold_of_compile_ok_supported
            spec selectors hSupported irContract tx hcompile fn hFind)
        hSourceParams hSourceBody with
    ⟨nativeContract, hLower, hMatch⟩
  exact
    ⟨nativeContract, hLower,
      compile_preserves_native_evmYulLean_of_nativeGeneratedCallDispatcherResult_match
        spec selectors hSupported irContract tx initialWorld observableSlots
        nativeContract htxNormalized hcalldataSizeFits hcompile hMatch⟩

/-- Closed generated `callDispatcher` theorem for a selected single-argument
return body `mstore(0, calldataload(4)); return(0, 32)`. -/
private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_mstore0_calldataload4_return32
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (hArgsCons : ∃ arg rest, tx.args = arg :: rest)
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap
      (NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_mstore0_calldataload4_return32
        irContract tx state observableSlots hArgsCons hReturnBody)
      hThreshold

/-- Closed generated `callDispatcher` theorem for a selected aligned-argument
return body `mstore(0, calldataload(4 + 32*idx)); return(0, 32)`. -/
private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_mstore0_calldataload_aligned_return32
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (idx arg : Nat)
    (rest : List Nat)
    (hArgDrop : tx.args.drop idx = arg :: rest)
    (hOffset64 : 4 + 32 * idx < 2 ^ 64)
    (hReturnBody :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit (4 + 32 * idx)]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap
      (NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_mstore0_calldataload_aligned_return32
        irContract tx state observableSlots idx arg rest hArgDrop hOffset64
        hReturnBody)
      hThreshold

/-- Named SimpleStorage native dispatcher direct-match obligation.

The lowered native dispatcher result is compared with `interpretIR` directly
instead of with the EVMYulLean fuel wrapper. -/
private def simpleStorageNativeCallDispatcherMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    Compiler.SimpleStorageNativeWitness.nativeContract

/-! ### Per-case sub-bridges for the SimpleStorage native dispatcher. -/

/-- Direct-match per-case sub-bridge for the `retrieve()` selector hit. -/
private def simpleStorageNativeRetrieveHitMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  tx.functionSelector % Compiler.Constants.selectorModulus = 0x2e64cec1 →
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    Compiler.SimpleStorageNativeWitness.nativeContract

/-- Direct-match per-case sub-bridge for the `store(uint256)` selector hit. -/
private def simpleStorageNativeStoreHitMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  tx.functionSelector % Compiler.Constants.selectorModulus = 0x6057361d →
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    Compiler.SimpleStorageNativeWitness.nativeContract

/-- Direct-match per-case sub-bridge for the selector-miss revert arm. -/
private def simpleStorageNativeSelectorMissMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  tx.functionSelector % Compiler.Constants.selectorModulus ≠ 0x2e64cec1 →
  tx.functionSelector % Compiler.Constants.selectorModulus ≠ 0x6057361d →
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    Compiler.SimpleStorageNativeWitness.nativeContract

/-- Retrieve-hit direct-match native dispatcher bridge. -/
private theorem simpleStorageNativeRetrieveHitMatchBridge_proved
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hdispatchGuardSafe : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      DispatchGuardsSafe fn tx) :
    simpleStorageNativeRetrieveHitMatchBridge tx initialState observableSlots := by
  intro hRetrieve
  have hSelectorEq : tx.functionSelector = 0x2e64cec1 := by
    have hmod := Nat.mod_eq_of_lt hselector
    rw [hmod] at hRetrieve
    exact hRetrieve
  have hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0 := by
    let retrieveFn : IRFunction :=
      { name := "retrieve"
        selector := 0x2e64cec1
        params := []
        ret := IRType.uint256
        body := [
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore" [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "return" [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])
        ] }
    have hmem : retrieveFn ∈ simpleStorageIRContract.functions := by
      simp [retrieveFn, simpleStorageIRContract]
    have hguards := hdispatchGuardSafe retrieveFn hmem
    have hzero : tx.msgValue % evmModulus = 0 := by
      rcases hguards with ⟨hValue, _⟩
      rcases hValue with hPayable | hZero
      · simp [retrieveFn] at hPayable
      · exact hZero
    simpa [evmModulus, EvmYul.UInt256.size] using hzero
  have hIR := interpretIR_simpleStorage_retrieveHit tx initialState hSelectorEq
    (by simpa [evmModulus, EvmYul.UInt256.size] using hMsgValue)
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode simpleStorageIRContract) observableSlots
  let shared :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      Compiler.SimpleStorageNativeWitness.nativeContract yulTx
      initialState.storage slots
  let p := shared.sload (EvmYul.UInt256.ofNat 0)
  let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
  let shared2 : EvmYul.SharedState .Yul :=
    { shared1 with
      toMachineState :=
        shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
  let shared3 : EvmYul.SharedState .Yul :=
    { shared2 with
      toMachineState :=
        shared2.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
  obtain ⟨store, hExec⟩ :=
    simpleStorageNativeContract_dispatcherExec_retrieveHit_halt_atFuel
      yulTx initialState.storage slots
      (by
        simp [yulTx]
        exact hRetrieve.symm)
      (by simpa [yulTx, YulTransaction.ofIR, evmModulus,
        Verity.Core.UINT256_MODULUS] using hNoWrap)
      (by simpa [yulTx, YulTransaction.ofIR] using hMsgValue)
  have hSlotZero : 0 ∈ slots := by
    simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots]
  have hp :
      p.2 = initialState.storage (IRStorageSlot.ofNat 0) := by
    have hload :=
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_sload_materializedSlot_value
        Compiler.SimpleStorageNativeWitness.nativeContract yulTx initialState.storage
        slots 0 hSlotZero
    have hsload := congrArg
      (fun s : EvmYul.State .Yul =>
        (s.sload (EvmYul.UInt256.ofNat 0)).2)
      (nativeSwitchPostInitFreeMemorySharedState_toState
        Compiler.SimpleStorageNativeWitness.nativeContract yulTx
        initialState.storage slots)
    exact (by simpa [p, shared] using hsload.trans hload)
  have hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) initialState.storage initialState.events
        (.error (EvmYul.Yul.Exception.YulHalt
          (EvmYul.Yul.State.Ok shared3 store) ⟨1⟩)) =
      { success := true,
        returnValue := some p.2.toNat,
        finalStorage :=
          Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
            (YulTransaction.ofIR tx) (EvmYul.Yul.State.Ok shared3 store),
        finalMappings :=
          Compiler.Proofs.storageAsMappings
            (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              (YulTransaction.ofIR tx) (EvmYul.Yul.State.Ok shared3 store)),
        events :=
          initialState.events ++
            Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
              (EvmYul.Yul.State.Ok shared3 store) } := by
    have hMemorySize : 32 ≤ shared.memory.size := by
      simpa [shared] using
        nativeSwitchPostInitFreeMemorySharedState_memory_size_ge_32
          Compiler.SimpleStorageNativeWitness.nativeContract yulTx
          initialState.storage slots
    simpa [yulTx, shared, p, shared1, shared2, shared3] using
      projectResult_retrieveHit_eq yulTx initialState.storage initialState.events
        shared store hMemorySize
  have hLogs :
      Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
        (EvmYul.Yul.State.Ok shared3 store) = [] := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
      shared3, shared2, shared1, p, shared,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.State.sload, EvmYul.State.addAccessedStorageKey,
      EvmYul.Substate.addAccessedStorageKey, EvmYul.Yul.State.sharedState]
    rfl
  apply nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match
    (haltState := EvmYul.Yul.State.Ok shared3 store) (haltValue := ⟨1⟩)
  · simpa [simpleStorage_runtimeCode_eq_single_dispatcher, yulTx, slots,
      shared, p, shared1, shared2, shared3] using hExec
  · exact hProject
  · rw [hIR]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [hp, Compiler.Proofs.IRGeneration.IRStorageWord.toNat]
    · intro slot hslot
      have hslot' : slot ∈ slots := by
        simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
          hslot]
      have hNative :=
        Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState_retrieveHit_initialState_materialized
          Compiler.SimpleStorageNativeWitness.nativeContract yulTx initialState.storage
          slots store slot hslot'
      exact hNative.symm
    · rw [hLogs, List.append_nil]

/-- Store-hit direct-match native dispatcher bridge.

The proof splits on the setter calldata argument. Short calldata projects the
native argument-guard revert directly to the IR arity failure; present calldata
uses the closed-form native store halt and compares projected storage on the
materialized observable slots. -/
private theorem simpleStorageNativeStoreHitMatchBridge_proved
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hdispatchGuardSafe : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      DispatchGuardsSafe fn tx) :
    simpleStorageNativeStoreHitMatchBridge tx initialState observableSlots := by
  intro hStore
  have hSelectorEq : tx.functionSelector = 0x6057361d := by
    have hmod := Nat.mod_eq_of_lt hselector
    rw [hmod] at hStore
    exact hStore
  have hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0 := by
    let storeFn : IRFunction :=
      { name := "store"
        selector := 0x6057361d
        params := [{ name := "value", ty := IRType.uint256 }]
        ret := IRType.unit
        body := [
          Yul.YulStmt.let_ "value" (Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "sstore" [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
          Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])
        ] }
    have hmem : storeFn ∈ simpleStorageIRContract.functions := by
      simp [storeFn, simpleStorageIRContract]
    have hguards := hdispatchGuardSafe storeFn hmem
    have hzero : tx.msgValue % evmModulus = 0 := by
      rcases hguards with ⟨hValue, _⟩
      rcases hValue with hPayable | hZero
      · simp [storeFn] at hPayable
      · exact hZero
    simpa [evmModulus, EvmYul.UInt256.size] using hzero
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode simpleStorageIRContract) observableSlots
  cases hArgs : tx.args with
  | nil =>
      have hIR := interpretIR_simpleStorage_storeHit_short tx initialState
        hSelectorEq hArgs
      refine nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
        (err := EvmYul.Yul.Exception.Revert)
        (nativeYul :=
          { success := false
            returnValue := none
            finalStorage := initialState.storage
            finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
            events := initialState.events })
        ?_ ?_ ?_
      · simpa [simpleStorage_runtimeCode_eq_single_dispatcher, yulTx, slots] using
          (simpleStorageNativeContract_dispatcherExec_storeHit_short_revert_atFuel
            yulTx initialState.storage slots
            (by simpa [yulTx, YulTransaction.ofIR] using hArgs)
            (by
              simp [yulTx]
              exact hStore.symm)
            (by simpa [yulTx, YulTransaction.ofIR, evmModulus,
              Verity.Core.UINT256_MODULUS] using hNoWrap)
            (by simpa [yulTx, YulTransaction.ofIR] using hMsgValue))
      · rfl
      · rw [hIR]
        exact ⟨rfl, rfl, (by intro slot _; rfl), rfl⟩
  | cons arg rest =>
      have hIR := interpretIR_simpleStorage_storeHit_arg tx initialState arg rest
        hSelectorEq hArgs
        (by simpa [evmModulus, EvmYul.UInt256.size] using hMsgValue)
      obtain ⟨store, haltState, hExec, hHaltState⟩ :=
        simpleStorageNativeContract_dispatcherExec_storeHit_halt_atFuel
          yulTx initialState.storage slots arg rest
          (by simpa [yulTx, YulTransaction.ofIR] using hArgs)
          (by
            simp [yulTx]
            exact hStore.symm)
          (by simpa [yulTx, YulTransaction.ofIR, evmModulus,
            Verity.Core.UINT256_MODULUS] using hNoWrap)
          (by simpa [yulTx, YulTransaction.ofIR] using hMsgValue)
      have hProject :
          Compiler.Proofs.YulGeneration.Backends.Native.projectResult
            (YulTransaction.ofIR tx) initialState.storage initialState.events
            (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨0⟩)) =
          { success := true,
            returnValue := none,
            finalStorage :=
              Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
                (YulTransaction.ofIR tx) haltState,
            finalMappings :=
              Compiler.Proofs.storageAsMappings
                (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
                  (YulTransaction.ofIR tx) haltState),
            events :=
              initialState.events ++
                Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
                  haltState } := by
        simp
      have hLogs :
          Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
            haltState = [] := by
        subst hHaltState
        simp only [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
          EvmYul.Yul.State.sharedState,
          EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
          EvmYul.Yul.State.insert, EvmYul.State.sstore,
          EvmYul.State.setAccount, EvmYul.State.lookupAccount,
          EvmYul.State.addAccessedStorageKey,
          EvmYul.Account.updateStorage,
          EvmYul.Substate.addAccessedStorageKey, Option.option]
        split <;> rfl
      apply nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match
        (haltState := haltState) (haltValue := ⟨0⟩)
      · simpa [simpleStorage_runtimeCode_eq_single_dispatcher, yulTx, slots] using hExec
      · exact hProject
      · rw [hIR]
        refine ⟨rfl, rfl, ?_, ?_⟩
        · intro slot hslot
          have hslot' : slot ∈ slots := by
            simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
              hslot]
          have hNative :=
            projectStorageFromState_storeHit_postInit_materialized
              Compiler.SimpleStorageNativeWitness.nativeContract yulTx
              initialState.storage slots store arg slot hslot'
          have hArgMod :
              EvmYul.UInt256.ofNat arg =
                EvmYul.UInt256.ofNat (arg % evmModulus) := by
            unfold EvmYul.UInt256.ofNat
            simp [Id.run, Fin.ofNat, evmModulus, EvmYul.UInt256.size]
          simpa [hHaltState,
            Compiler.Proofs.abstractStoreStorageOrMapping,
            Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, hArgMod] using hNative.symm
        · rw [hLogs, List.append_nil]

/-- Selector-miss direct-match native dispatcher bridge.

The native selector-miss path projects to the same revert result as the IR
selector-miss interpreter case, so this proof avoids the compatibility
fuel-wrapper bridge entirely. -/
private theorem simpleStorageNativeSelectorMissMatchBridge_proved
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus) :
    simpleStorageNativeSelectorMissMatchBridge tx initialState observableSlots := by
  intro hSelMissRetrieve hSelMissStore
  have hSelEq : tx.functionSelector % selectorModulus = tx.functionSelector :=
    Nat.mod_eq_of_lt hselector
  have hSelMissTxStore : tx.functionSelector ≠ 0x6057361d := by
    rw [← hSelEq]
    exact hSelMissStore
  have hSelMissTxRetrieve : tx.functionSelector ≠ 0x2e64cec1 := by
    rw [← hSelEq]
    exact hSelMissRetrieve
  have hIR := interpretIR_simpleStorage_selectorMiss tx initialState
    hSelMissTxStore hSelMissTxRetrieve
  refine nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
    (err := EvmYul.Yul.Exception.Revert)
    (nativeYul :=
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events })
    ?_ ?_ ?_
  · apply simpleStorageNativeContract_dispatcherExec_selectorMiss_revert_atFuel
    · have hMod :
          (YulTransaction.ofIR tx).functionSelector
            % Compiler.Constants.selectorModulus
            < Compiler.Constants.selectorModulus :=
        Nat.mod_lt _ (by decide)
      exact Nat.lt_trans hMod (by decide)
    · change (YulTransaction.ofIR tx).functionSelector % selectorModulus ≠ _
      change tx.functionSelector % selectorModulus ≠ _
      exact hSelMissStore
    · change (YulTransaction.ofIR tx).functionSelector % selectorModulus ≠ _
      change tx.functionSelector % selectorModulus ≠ _
      exact hSelMissRetrieve
    · change 4 + (YulTransaction.ofIR tx).args.length * 32 < EvmYul.UInt256.size
      change 4 + tx.args.length * 32 < EvmYul.UInt256.size
      simpa [evmModulus, EvmYul.UInt256.size] using hNoWrap
  · rfl
  · rw [hIR]
    exact ⟨rfl, rfl, (by intro slot _; rfl), rfl⟩

/-- Recover the direct-match monolithic SimpleStorage dispatcher obligation
from the three direct per-case sub-bridges. -/
private theorem simpleStorageNativeCallDispatcherMatchBridge_of_per_case
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hRetrieveHit :
      simpleStorageNativeRetrieveHitMatchBridge tx initialState observableSlots)
    (hStoreHit :
      simpleStorageNativeStoreHitMatchBridge tx initialState observableSlots)
    (hSelectorMiss :
      simpleStorageNativeSelectorMissMatchBridge tx initialState observableSlots) :
    simpleStorageNativeCallDispatcherMatchBridge tx initialState observableSlots := by
  unfold simpleStorageNativeCallDispatcherMatchBridge
  by_cases hR :
      tx.functionSelector % Compiler.Constants.selectorModulus = 0x2e64cec1
  · exact hRetrieveHit hR
  · by_cases hS :
        tx.functionSelector % Compiler.Constants.selectorModulus = 0x6057361d
    · exact hStoreHit hS
    · exact hSelectorMiss hR hS

/-- Native SimpleStorage end-to-end theorem over the direct projected
`EvmYul.Yul.callDispatcher` result. -/
theorem simpleStorage_endToEnd_native_evmYulLean
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hdispatchGuardSafe : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      DispatchGuardsSafe fn tx) :
    nativeResultsMatchOn observableSlots
      (interpretIR simpleStorageIRContract tx initialState)
      (nativeGeneratedCallDispatcherResultOf simpleStorageIRContract tx
        initialState observableSlots
        Compiler.SimpleStorageNativeWitness.nativeContract) := by
  have hConcrete :
      simpleStorageNativeCallDispatcherMatchBridge tx initialState
        observableSlots :=
    simpleStorageNativeCallDispatcherMatchBridge_of_per_case
      tx initialState observableSlots
      (simpleStorageNativeRetrieveHitMatchBridge_proved tx initialState
        observableSlots hselector hNoWrap hdispatchGuardSafe)
      (simpleStorageNativeStoreHitMatchBridge_proved tx initialState
        observableSlots hselector hNoWrap hdispatchGuardSafe)
      (simpleStorageNativeSelectorMissMatchBridge_proved tx initialState
        observableSlots hselector hNoWrap)
  unfold simpleStorageNativeCallDispatcherMatchBridge at hConcrete
  unfold nativeDispatcherExecMatchesIRPositive at hConcrete
  unfold nativeGeneratedCallDispatcherResultOf
  dsimp at hConcrete ⊢
  rw [
    Compiler.Proofs.YulGeneration.Backends.Native.callDispatcher_succ_eq_callDispatcherBlockResult,
    Compiler.Proofs.YulGeneration.Backends.Native.callDispatcherBlockResult_initialState_eq_contractDispatcherBlockResult,
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherBlockResult_eq_execResult
  ]
  convert hConcrete using 1 <;>
    simp [simpleStorageNativeDispatcherFuel, simpleStorage_runtimeCode_eq_single_dispatcher,
      EvmYul.Yul.Ast.FunctionDefinition.rets] <;> rfl

/-- Source-level SimpleStorage native theorem from any already established
source-to-IR result match.

The concrete native dispatcher bridge proves `interpretIR` agrees with the
projected `EvmYul.Yul.callDispatcher` result; this wrapper composes that fact
with the standard source-to-IR result surface. -/
theorem simpleStorage_source_endToEnd_native_evmYulLean_of_sourceIR
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (source : SourceSemantics.SourceContractResult)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hdispatchGuardSafe : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      DispatchGuardsSafe fn tx)
    (hSourceIR :
      Compiler.Proofs.IRGeneration.FunctionBody.sourceResultMatchesIRResult
        source (interpretIR simpleStorageIRContract tx initialState)) :
    sourceResultMatchesNativeOn observableSlots source
      (nativeGeneratedCallDispatcherResultOf simpleStorageIRContract tx
        initialState observableSlots
        Compiler.SimpleStorageNativeWitness.nativeContract) := by
  exact
    sourceResultMatchesNativeOn_of_sourceResultMatchesIRResult_of_nativeResultsMatchOn
      hSourceIR
      (simpleStorage_endToEnd_native_evmYulLean tx initialState observableSlots
        hselector hNoWrap hdispatchGuardSafe)

/-- Denote-headed SimpleStorage native theorem: the compiler-free denotation of
an event-free function matches the projected `EvmYul.Yul.callDispatcher` result
whenever the trusted source interpretation matches the IR result. -/
theorem simpleStorage_denote_endToEnd_native_evmYulLean_of_sourceIR
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (spec : CompilationModel.CompilationModel)
    (fn : CompilationModel.FunctionSpec)
    (initialWorld : Verity.ContractState)
    (hnoEvents : spec.events = [])
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hdispatchGuardSafe : ∀ fn', fn' ∈ simpleStorageIRContract.functions →
      DispatchGuardsSafe fn' tx)
    (hSourceIR :
      Compiler.Proofs.IRGeneration.FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunction spec fn tx initialWorld)
        (interpretIR simpleStorageIRContract tx initialState)) :
    denoteResultMatchesNativeOn observableSlots
      (CompilationModel.Denote.denoteFunction DenoteAgreement.sourceOracle spec fn
        (DenoteAgreement.ofIRTransaction tx) initialWorld)
      (nativeGeneratedCallDispatcherResultOf simpleStorageIRContract tx
        initialState observableSlots
        Compiler.SimpleStorageNativeWitness.nativeContract) :=
  denoteResultMatchesNativeOn_of_sourceResultMatchesNativeOn hnoEvents
    (simpleStorage_source_endToEnd_native_evmYulLean_of_sourceIR tx initialState
      observableSlots _ hselector hNoWrap hdispatchGuardSafe hSourceIR)

/-! ## Universal Pure Arithmetic Bridge

The pure arithmetic bridge proofs (`pure_add_bridge`, etc.) were removed
after the older builtin-routing wrapper grew `callvalue`/`calldatasize`
support, making the monolithic wrapper too large for the default
heartbeat limit during type-checking. The proofs were mathematically
correct but need that builtin-routing surface to be factored into smaller
pieces before they can be re-stated without timeout.

See: `ArithmeticProfile.lean` and
`YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean` for the current
replacement coverage: universal bridge lemmas for all pure bridged builtins.
-/

/-! ## EVMYulLean Semantic Targets

The public native theorem surface in this file targets the direct projected
`EvmYul.Yul.callDispatcher` result through `nativeGeneratedCallDispatcherResultOf`.
The older `nativeIRRuntimeMatchesIR` and generated dispatcher-exec theorem
families remain file-local transition evidence. EndToEnd no longer defines
compatibility wrappers over the older backend-parameterized transition surface.

The private backend-fuel transition module that previously recorded
bridge-history facts has been removed (DoD 5 of the EVMYulLean transition).
The file-local `runtimeCode_bridged_local` lemma in this module retains the
emitted-runtime closure witness, and the SupportedSpec-discharged variants
`emitYul_runtimeCode_bridged_of_compile_ok_supported` and
`emitYul_runtimeCode_bridged_of_compile_ok_supported_except_mapping_writes_stmt_safety`
expose the public surface this file needs.
  The body-closure increments prove that generated external function bodies can
  discharge raw `BridgedStmts` witnesses from `SupportedSpec`, static-parameter
  witnesses, and `BridgedSafeStmts` source-body witnesses.
  Body-closure increments also prove scalar and static-scalar calldata
  parameter prologues satisfy `BridgedStmts`, pure source-expression fragments
  compile to `BridgedExpr`, and universal `compileStmtList_always_bridged`
  coverage for source bodies admitted by `BridgedSafeStmts`.

**Trust boundary after Phase 4 (recursive statement-target fragment)**:
- For any single bridged-builtin call whose bridge dependencies are fully
  proven, the Yul semantics trust assumption shifts from "Verity's custom
  builtin implementations are correct" to "EVMYulLean's execution model
  matches the EVM" (backed by upstream Ethereum conformance tests).
- `BridgedTarget` statement and statement-list executions inherit that same
  backend equivalence when their nested statements satisfy `BridgedStmt`.
- The generated runtime dispatch wrapper is now known to satisfy `BridgedTarget`
  and execute equivalently under the EVMYulLean backend when the IR bodies it
  embeds satisfy `BridgedStmt`.
- Layer 3 no longer keeps EndToEnd compatibility lemmas targeting the
  older EVMYulLean backend-fuel surface; the public EndToEnd theorem family
  targets native dispatcher execution through the direct projected
  `nativeGeneratedCallDispatcherResultOf` result.
- The historical Verity-backed public oracle-routed EndToEnd wrappers
  have been removed.
- Scalar and static-scalar calldata parameter-loading prologues are now known
  to satisfy `BridgedStmts`.
- The `ExprCompileCore` expression grammar is now known to lift into
  `BridgedSourceExpr`, including environment reads, `calldatasize`,
  branchless helpers, and calldata/memory/transient unary reads.
- Singleton `mstore`/`tstore` bodies whose offset and value are
  `ExprCompileCore` are now known to satisfy `BridgedSafeStmts`, matching the
  `SupportedFragment.mstoreSingle` and `SupportedFragment.tstoreSingle`
  source shapes.
- Simple `setStorage`, `setStorageAddr`, and `require` source-body lists now
  have direct `BridgedSafeStmts` constructors. The singleton uint/address
  storage and literal guard-family shapes exposed by `SupportedFragment` can be
  discharged from their compile-core and field-layout witnesses.
- Scalar-leaf and pure-expression `letVar`/`assignVar` statement lists are now
  known to compile to `BridgedStmts`.
- External `StmtListCompileCore` and `StmtListTerminalCore` bodies now have
  direct `BridgedSafeStmts` packagers through the native recursive raw-log
  source fragment.
- Pure-binding plus unpacked single-slot `setStorage` statement lists and
  external `stop`/`return` terminators are now known to compile to
  `BridgedStmts`.
- Internal `return` terminators are now known to compile to assignment-plus-
  `leave` `BridgedStmts`.
- Plain `Stmt.require` statement lists with bridged failure conditions are
  now known to compile to `BridgedStmts` (the generated revert-message body
  is hypothesis-free).
- 36 of 36 builtins are bridged, including `mappingSlot` via the shared
  keccak-faithful `abstractMappingSlot` derivation.
- All bridge lemmas are complete; all builtin bridge equivalences are proven.
- Statement-position `internalCall` / `internalCallAssign` and
  `externalCallBind` source bodies are admitted into `BridgedSafeStmts` when
  their compiled callees resolve in an explicit `BridgedFunctionTable`; opaque
  ECM statements remain outside the safe-body wrapper until concrete modules
  provide bridgeable-output obligations.

The Phase 4 backend-fuel module has been removed; the equivalent transition
theorems are no longer needed because the public EndToEnd surface targets
EVMYulLean's native dispatcher execution directly via
`nativeGeneratedCallDispatcherResultOf`.
-/

end Compiler.Proofs.EndToEnd
