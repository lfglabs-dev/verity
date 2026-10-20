import Compiler.Proofs.EndToEnd.Base

namespace Compiler.Proofs.EndToEnd

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends

/-! Local abbreviations for recurring SimpleStorage native-witness terms. -/
local notation:max "ssNC" => SimpleStorageNativeWitness.nativeContract
local notation:max "ssInit" => Backends.Native.initialState ssNC
local notation:max "ssPost" => Backends.Native.nativeSwitchPostInitFreeMemoryState ssNC
local notation:max "ssShared" => Backends.Native.nativeSwitchPostInitFreeMemorySharedState ssNC
local notation:max "ssSelExpr" => Yul.YulExpr.call "shr"
  [Yul.YulExpr.lit Constants.selectorShift, Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]]
local notation:max "ssRuntime" => [CodegenCommon.initFreeMemoryPointer,
  CodegenCommon.buildSwitch simpleStorageIRContract.functions none none]
local notation:max "ssReservedNames" => Backends.yulStmtsIdentifierNames ssRuntime
local notation:max "ssHasSelRhs" => Backends.lowerExprNative (Yul.YulExpr.call "iszero"
  [Yul.YulExpr.call "lt" [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]])
local notation:max "ssMissCond" => Backends.lowerExprNative
  (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident "__has_selector"])
local notation:max "ssHitCond" => Backends.lowerExprNative (Yul.YulExpr.ident "__has_selector")
local notation:max "ssSwitchBlock(" rn ", " n0 ", " cs ")" =>
  Backends.lowerNativeSwitchBlock ssSelExpr (Backends.freshNativeSwitchId rn n0) cs
    [Backends.Native.nativeRevertZeroZeroStmt]
local notation:max "ssInitFMP" => Backends.lowerExprNative
  (Yul.YulExpr.call "mstore" [Yul.YulExpr.lit Constants.freeMemoryPointer, Yul.YulExpr.lit 128])

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
- Singleton `calldatacopy` bodies whose destination, source, and size are
  `ExprCompileCore` are now known to satisfy `BridgedSafeStmts`, matching the
  `SupportedFragment.calldatacopySingle` source shape. The copied region is
  modeled word-wise against the frame's calldata, so `calldatacopy` no longer
  belongs to the unsupported low-level surface.
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

/-! ## Concrete Instantiation: SimpleStorage -/

/-- The emitted SimpleStorage runtime consists of the single generated external
dispatcher shell for the two concrete SimpleStorage functions.

This pins down the outer runtime layer that the native dispatcher bridge must
peel before applying the concrete lowered selector-switch lemmas. -/
private theorem simpleStorage_runtimeCode_eq_single_dispatcher :
    (Compiler.emitYul simpleStorageIRContract).runtimeCode =
      ssRuntime := by
  dsimp [Compiler.emitYul, CodegenCommon.emitYul,
    Compiler.runtimeCode, CodegenCommon.runtimeCode,
    simpleStorageIRContract]

private abbrev simpleStorageBuildSwitchSourceCases : List (Nat × List Yul.YulStmt) :=
  simpleStorageIRContract.functions.map (fun fn =>
    (fn.selector,
      CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
        ([CodegenCommon.calldatasizeGuard fn.params.length] ++ fn.body)))

private abbrev simpleStorageBuildSwitchBody : List Yul.YulStmt :=
  [Yul.YulStmt.let_ "__has_selector"
    (Yul.YulExpr.call "iszero"
      [Yul.YulExpr.call "lt"
        [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]),
   Yul.YulStmt.if_ (Yul.YulExpr.call "iszero"
      [Yul.YulExpr.ident "__has_selector"])
      (CodegenCommon.defaultDispatchCase none none),
   Yul.YulStmt.if_ (Yul.YulExpr.ident "__has_selector")
      [Yul.YulStmt.switch
        ssSelExpr
        simpleStorageBuildSwitchSourceCases
        (some (CodegenCommon.defaultDispatchCase none none))]]

private noncomputable def simpleStorageNativeRuntimeDispatcherStmts :
    List EvmYul.Yul.Ast.Stmt :=
  match
    Backends.lowerStmtsNative
      ssRuntime with
  | .ok stmts => stmts
  | .error _ => []

/-- The executable SimpleStorage native witness is exactly the statement
lowering of the single emitted dispatcher shell.

This exposes the concrete lowered dispatcher block without unfolding the
computed native witness in later selector-case proofs. -/
private theorem simpleStorageNativeContract_dispatcher_eq_lowered_stmts :
    (ssNC).dispatcher =
      .Block simpleStorageNativeRuntimeDispatcherStmts := by
  have hOuter := SimpleStorageNativeWitness.lowerRuntimeContractNative_eq
  obtain ⟨dispatcher, hDispatcher, hContract⟩ :=
    Backends.Native.lowerRuntimeContractNative_emitYul_noMapping_ok_dispatcher
      simpleStorageIRContract ssNC
      (by rfl) (by rfl) (by rfl) (by rfl) hOuter
  rw [hContract]
  simp [simpleStorageNativeRuntimeDispatcherStmts, hDispatcher]

/-- Lowering a two-statement `[exprStmt e, block body]` list exposes the
lowered inner block of `body`, threaded at the same switch-id counter. -/
private theorem lowerStmtsNativeWithSwitchIds_expr_block_ok
    (ids : List String) (n : Nat) (e : Yul.YulExpr) (body : List Yul.YulStmt)
    (lowered : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds ids n
      [.exprStmt e, .block body] = .ok (lowered, next)) :
    ∃ inner, lowered =
        [.ExprStmtCall (Backends.lowerExprNative e),
         .Block inner] ∧
      Backends.lowerStmtsNativeWithSwitchIds ids n body =
        .ok (inner, next) := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
    Backends.lowerStmtGroupNativeWithSwitchIds_expr] at h
  simp only [Bind.bind, Except.bind] at h
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
    Backends.lowerStmtGroupNativeWithSwitchIds_block] at h
  cases hBody :
      Backends.lowerStmtsNativeWithSwitchIds ids n body with
  | error err => simp [hBody, Bind.bind, Except.bind] at h
  | ok pair =>
      rcases pair with ⟨inner, k⟩
      simp [hBody, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨inner, rfl, rfl⟩

private theorem simpleStorage_buildSwitch_eq_block :
    CodegenCommon.buildSwitch simpleStorageIRContract.functions none none =
      Yul.YulStmt.block simpleStorageBuildSwitchBody := by
  rfl

/-- The SimpleStorage native dispatcher statement list is a singleton `.Block`.

Reason: `buildSwitch` produces a `Yul.YulStmt.block`, which the native lowering
maps to `[.Block inner]` for the lowered inner statements. Combined with the
fact that the lowering succeeds (above), this exposes the inner block shape
without further computation. -/
private theorem simpleStorageNativeRuntimeDispatcherStmts_exists_init_block :
    ∃ (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat),
      simpleStorageNativeRuntimeDispatcherStmts = [.ExprStmtCall ssInitFMP, .Block inner] ∧
      Backends.lowerStmtsNativeWithSwitchIds ssReservedNames 0 simpleStorageBuildSwitchBody =
        .ok (inner, next) := by
  obtain ⟨dispatcher, hDispatcher, -⟩ :=
    Backends.Native.lowerRuntimeContractNative_emitYul_noMapping_ok_dispatcher
      simpleStorageIRContract ssNC (by rfl) (by rfl) (by rfl) (by rfl)
      SimpleStorageNativeWitness.lowerRuntimeContractNative_eq
  unfold simpleStorageNativeRuntimeDispatcherStmts
  rw [hDispatcher]
  unfold Backends.lowerStmtsNative at hDispatcher
  cases hLowerList : Backends.lowerStmtsNativeWithSwitchIds ssReservedNames 0 ssRuntime with
  | error err => simp [hLowerList, Bind.bind, Except.bind] at hDispatcher
  | ok pair =>
      rcases pair with ⟨lowered, finalNext⟩
      simp [hLowerList, Bind.bind, Except.bind, Pure.pure, Except.pure] at hDispatcher
      subst dispatcher
      rw [simpleStorage_buildSwitch_eq_block] at hLowerList
      obtain ⟨inner, rfl, hInner⟩ :=
        lowerStmtsNativeWithSwitchIds_expr_block_ok _ _ _ _ _ _ hLowerList
      exact ⟨inner, finalNext, by simp, hInner⟩

private noncomputable def simpleStorageNativeDispatcherInnerStmts :
    List EvmYul.Yul.Ast.Stmt :=
  Classical.choose simpleStorageNativeRuntimeDispatcherStmts_exists_init_block

private noncomputable def simpleStorageNativeDispatcherInnerNext : Nat :=
  Classical.choose
    (Classical.choose_spec simpleStorageNativeRuntimeDispatcherStmts_exists_init_block)

private theorem simpleStorageNativeRuntimeDispatcherStmts_eq_init_block :
    simpleStorageNativeRuntimeDispatcherStmts =
      [.ExprStmtCall ssInitFMP, .Block simpleStorageNativeDispatcherInnerStmts] :=
  (Classical.choose_spec
    (Classical.choose_spec
      simpleStorageNativeRuntimeDispatcherStmts_exists_init_block)).1

private theorem simpleStorageNativeDispatcherInnerStmts_lowering_ok :
    Backends.lowerStmtsNativeWithSwitchIds ssReservedNames 0 simpleStorageBuildSwitchBody =
      .ok (simpleStorageNativeDispatcherInnerStmts, simpleStorageNativeDispatcherInnerNext) :=
  (Classical.choose_spec
    (Classical.choose_spec
      simpleStorageNativeRuntimeDispatcherStmts_exists_init_block)).2

/-- Transitive form of the SimpleStorage native dispatcher shape: combining
the lowered-stmts and singleton-block equalities exposes the dispatcher value
as `.Block [.Block <inner>]`, which is the exact shape consumed by the harness
dispatcher-exec peel lemma. -/
private theorem simpleStorageNativeContract_dispatcher_eq_singleton_block_inner :
    (ssNC).dispatcher =
      .Block [.ExprStmtCall ssInitFMP, .Block simpleStorageNativeDispatcherInnerStmts] := by
  rw [simpleStorageNativeContract_dispatcher_eq_lowered_stmts]
  congr
  exact simpleStorageNativeRuntimeDispatcherStmts_eq_init_block

/-- Reify the SimpleStorage native witness contract as a record whose
dispatcher is the doubly-blocked inner statement list.

This packages record-η with the lowered + singleton-block dispatcher
equalities so that the harness peel lemmas (which expect a
`{ dispatcher := .Block body, functions := … }` shape) apply in one rewrite. -/
private theorem simpleStorageNativeContract_eq_record_inner_block :
    ssNC =
      { dispatcher := .Block [.ExprStmtCall ssInitFMP, .Block simpleStorageNativeDispatcherInnerStmts]
        functions := (ssNC).functions } := by
  have hEta : ssNC =
      (⟨(ssNC).dispatcher, (ssNC).functions⟩ : EvmYul.Yul.Ast.YulContract) := rfl
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
    Backends.Native.contractDispatcherExecResult (Nat.succ (Nat.succ (peeledFuel + 6))) ssNC
        (ssInit tx storage observableSlots) =
      EvmYul.Yul.exec (peeledFuel + 5) (.Block simpleStorageNativeDispatcherInnerStmts)
        (some ssNC) (ssPost tx storage observableSlots ∅) := by
  rw [simpleStorageNativeContract_eq_record_inner_block,
    Backends.Native.contractDispatcherExecResult_block_dispatcher_eq_exec_block (peeledFuel + 6)
      [.ExprStmtCall ssInitFMP, .Block simpleStorageNativeDispatcherInnerStmts]
      (ssNC).functions tx storage observableSlots,
    Backends.Native.exec_block_cons_initFreeMemoryPointer_eq
      peeledFuel [.Block simpleStorageNativeDispatcherInnerStmts]
      { dispatcher := .Block [.ExprStmtCall ssInitFMP, .Block simpleStorageNativeDispatcherInnerStmts],
        functions := (ssNC).functions }
      tx storage observableSlots,
    show peeledFuel + 6 = Nat.succ (Nat.succ (peeledFuel + 4)) by omega,
    Backends.Native.exec_singleton_block_eq_exec_block]

/-- Core decomposition of the lowered SimpleStorage dispatcher inner block: the
concrete `let __has_selector`, selector-miss `if`, and selector-hit `if` heads, with
the selector-hit body still exposed as the native lowering of the source `switch`.
The trailing list is empty because `buildSwitch` emits a 3-statement block. -/
private theorem simpleStorageNativeDispatcherInnerStmts_decomp :
    ∃ (body1 body2 : List EvmYul.Yul.Ast.Stmt) (n1 n2 : Nat),
      simpleStorageNativeDispatcherInnerStmts =
        [.Let ["__has_selector"] (some ssHasSelRhs), .If ssMissCond body1,
          .If ssHitCond body2] ∧
      Backends.lowerStmtsNativeWithSwitchIds ssReservedNames n1
        [Yul.YulStmt.switch ssSelExpr simpleStorageBuildSwitchSourceCases
          (some (CodegenCommon.defaultDispatchCase none none))] = .ok (body2, n2) := by
  obtain ⟨rest, hLet, hRest⟩ := Backends.Native.lowerStmtsNativeWithSwitchIds_let_head_eq
    _ _ _ _ _ _ _ simpleStorageNativeDispatcherInnerStmts_lowering_ok
  obtain ⟨body1, n1, rest', hIf1, -, hRest1⟩ :=
    Backends.Native.lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest
  obtain ⟨body2, n2, rest'', hIf2, hBody2, hRest2⟩ :=
    Backends.Native.lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Backends.lowerStmtsNativeWithSwitchIds_nil, Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨rfl, -⟩ := hRest2
  exact ⟨body1, body2, n1, n2, by rw [hLet, hIf1, hIf2], hBody2⟩

/-- The full inner-block of the SimpleStorage native dispatcher has the expected
three-statement `let`/`if`/`if` shape. -/
private theorem simpleStorageNativeDispatcherInnerStmts_eq_let_if_if :
    ∃ (e : EvmYul.Yul.Ast.Expr) (c1 : EvmYul.Yul.Ast.Expr)
      (body1 : List EvmYul.Yul.Ast.Stmt)
      (c2 : EvmYul.Yul.Ast.Expr) (body2 : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"] (some e),
         EvmYul.Yul.Ast.Stmt.If c1 body1,
         EvmYul.Yul.Ast.Stmt.If c2 body2] := by
  obtain ⟨body1, body2, -, -, h, -⟩ := simpleStorageNativeDispatcherInnerStmts_decomp
  exact ⟨_, _, body1, _, body2, h⟩

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


/-- Concrete head exposure of the SimpleStorage native dispatcher inner-block:
its first statement is the lowered `let __has_selector := iszero(lt(calldatasize(), 4))`
that `buildSwitch` emits, so the `Classical.choose`-pinned
`simpleStorageNativeDispatcher_letValue` can be equated to it via head injection. -/
private theorem simpleStorageNativeDispatcherInnerStmts_concrete_let_head :
    ∃ rest : List EvmYul.Yul.Ast.Stmt,
      simpleStorageNativeDispatcherInnerStmts =
        EvmYul.Yul.Ast.Stmt.Let ["__has_selector"] (some ssHasSelRhs) :: rest := by
  obtain ⟨_, _, _, _, h, -⟩ := simpleStorageNativeDispatcherInnerStmts_decomp
  exact ⟨_, h⟩

/-- Concrete-form equation for the SimpleStorage native dispatcher's full inner
3-statement block, pinning the let RHS and both guard conditions to the literal
Yul expressions emitted by `buildSwitch`; only the two `If` bodies stay
existential. -/
private theorem simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_if :
    ∃ (body1 body2 : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        [.Let ["__has_selector"] (some ssHasSelRhs), .If ssMissCond body1,
          .If ssHitCond body2] := by
  obtain ⟨body1, body2, -, -, h, -⟩ := simpleStorageNativeDispatcherInnerStmts_decomp
  exact ⟨body1, body2, h⟩

/-- Source-lowered companion of `_eq_concrete_let_if_if`: the selector-hit body is
the lowered revert-default switch block, and the lowering equation for the
buildSwitch-emitted source case list `simpleStorageBuildSwitchSourceCases` into the
lowered `cases'` is exposed. Chained with `lowerSwitchCasesNativeWithSwitchIds_tags_eq`
it converts source-level selector facts into lowered-level `find?` results. -/
private theorem simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default_sourceLowered :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      simpleStorageNativeDispatcherInnerStmts =
        [.Let ["__has_selector"] (some ssHasSelRhs), .If ssMissCond body1,
          .If ssHitCond [ssSwitchBlock(reservedNames, n0, cases')]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  obtain ⟨body1, body2, n1, -, h, hBody2⟩ := simpleStorageNativeDispatcherInnerStmts_decomp
  obtain ⟨cases', midN, rfl, hLowerCases⟩ :=
    Backends.Native.lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered
      _ _ _ _ _ _ hBody2
  exact ⟨body1, _, n1, cases', midN, h, hLowerCases⟩

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
      ssHasSelRhs := by
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
      ssMissCond := by
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
      ssHitCond := by
  obtain ⟨_, _, hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_if
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact hCombo.2.2.1.1

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
        [ssSwitchBlock(reservedNames, n0, cases')] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  obtain ⟨_, reservedNames, n0, cases', midN, hConcrete, hLowerCases⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default_sourceLowered
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact ⟨reservedNames, n0, cases', midN, hCombo.2.2.1.2, hLowerCases⟩

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
          (Backends.Native.nativeSwitchPostInitFreeMemoryState
            contract tx storage observableSlots ∅) =
        EvmYul.Yul.exec (fuel + 8)
          (.Block
            [ssSwitchBlock(reservedNames, n0, cases')])
          (some contract)
          ((Backends.Native.nativeSwitchPostInitFreeMemoryState
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
    [ssSwitchBlock(reservedNames, n0, cases')]
    hNoWrap

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
      Backends.Native.contractDispatcherExecResult
          (peeledFuel + 15)
          ssNC
          (ssInit tx storage observableSlots) =
        EvmYul.Yul.exec (peeledFuel + 8)
          (.Block
            [ssSwitchBlock(reservedNames, n0, cases')])
          (some ssNC)
          ((ssPost tx storage observableSlots ∅).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      peeledFuel ssNC
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
      selector = tx.functionSelector % Constants.selectorModulus)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFind : cases'.find? (fun entry => entry.1 == selector) = none)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size)
    (hReduction :
      Backends.Native.contractDispatcherExecResult
          (fuel + cases'.length + 20)
          ssNC
          (ssInit tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block
            [Backends.lowerNativeSwitchBlock
              ssSelExpr
              switchId cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some ssNC)
          ((ssPost tx storage observableSlots ∅).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1))) :
    Backends.Native.contractDispatcherExecResult
        (fuel + cases'.length + 20)
        ssNC
        (ssInit tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  rw [hReduction]
  exact (Backends.Native.exec_block_lowerNativeSwitchBlock_revert_default_postInitFreeMemory_hasSelectorState_projectResult_eq
    fuel selector switchId cases'
    ssNC
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
    (Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).executionEnv.weiValue =
      Backends.StateBridge.natToUInt256 tx.msgValue := by
  simp [Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    Backends.Native.initialState,
    Backends.StateBridge.toSharedState,
    YulState.initial, EvmYul.Yul.State.sharedState,
    Backends.StateBridge.mkBlockHeader]

private theorem nativeSwitchPostInitFreeMemorySharedState_calldata_size
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    (Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).executionEnv.calldata.size =
      4 + tx.args.length * 32 := by
  simp [Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    Backends.Native.initialState,
    Backends.StateBridge.toSharedState,
    YulState.initial, EvmYul.Yul.State.sharedState,
    Backends.StateBridge.mkBlockHeader,
    Backends.StateBridge.calldataToByteArray_size]

private theorem nativeSwitchPostInitFreeMemorySharedState_perm
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    (Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).executionEnv.perm = true := by
  simp [Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    Backends.Native.initialState,
    Backends.StateBridge.toSharedState,
    YulState.initial, EvmYul.Yul.State.sharedState,
    Backends.StateBridge.mkBlockHeader]

private theorem nativeSwitchPostInitFreeMemorySharedState_calldataload4
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest) :
    (Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).calldataload (EvmYul.UInt256.ofNat 4) =
      Backends.StateBridge.natToUInt256 arg := by
  simpa [Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    Backends.Native.initialState,
    EvmYul.Yul.State.sharedState, EvmYul.Yul.State.toState] using
    Backends.Native.initialState_calldataload4_arg0_word
      contract tx storage observableSlots arg rest hArgs

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
        Backends.StateBridge.natToUInt256 arg) :
    let initialWithStore : EvmYul.Yul.State := .Ok shared store
    let withValue := initialWithStore.insert "value"
      (Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Backends.StateBridge.natToUInt256 arg))
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
          (Backends.StateBridge.natToUInt256 arg)
          store)).executionEnv.perm = true := by
    simpa [EvmYul.Yul.State.executionEnv] using hPerm
  rw [show fuel + 7 = (fuel + 6) + 1 by omega]
  rw [Backends.Native.primCall_sstore_ok
    (fuel + 6) _ _ _ hPerm]
  rfl

/-- Post-init dispatcher calldata with at least one argument word fits in a
`UInt256` and is long enough for the `calldataload(4)` argument guard. -/
private theorem nativeSwitchPostInitFreeMemorySharedState_calldata_bounds_36
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    let shared :=
      Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        contract tx storage observableSlots
    shared.executionEnv.calldata.size < EvmYul.UInt256.size ∧
      36 ≤ shared.executionEnv.calldata.size := by
  intro shared
  have hCalldataSize : shared.executionEnv.calldata.size = 4 + tx.args.length * 32 :=
    nativeSwitchPostInitFreeMemorySharedState_calldata_size contract tx storage observableSlots
  refine ⟨by simpa [hCalldataSize] using hNoWrap, ?_⟩
  rw [hCalldataSize, hArgs]
  simp
  omega

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

/-- Composed body-level closed form for the SimpleStorage store hit-case when
the calldata contains the setter argument. -/
private theorem exec_block_simpleStorageLoweredStoreCaseBody_halt
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (tx : YulTransaction) (_storage : IRStorageSlot → IRStorageWord)
    (_observableSlots : List Nat) (store : EvmYul.Yul.VarStore)
    (arg : Nat) (rest : List Nat) (_hArgs : tx.args = arg :: rest)
    (hPerm : shared.executionEnv.perm = true)
    (hWord :
      shared.calldataload (EvmYul.UInt256.ofNat 4) =
        Backends.StateBridge.natToUInt256 arg)
    (hWei : shared.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal))
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 36 ≤ shared.executionEnv.calldata.size) :
    let initialWithStore : EvmYul.Yul.State :=
      .Ok shared store
    let withValue := initialWithStore.insert "value"
      (Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Backends.StateBridge.natToUInt256 arg))
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
    CodegenCommon.dispatchBody,
    CodegenCommon.callvalueGuard,
    CodegenCommon.calldatasizeGuard,
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
      selector = tx.functionSelector % Constants.selectorModulus)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hSelMissStore : selector ≠ 0x6057361d)
    (hSelMissRetrieve : selector ≠ 0x2e64cec1)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    Backends.Native.contractDispatcherExecResult
        (fuel + 22)
        ssNC
        (ssInit tx storage observableSlots) =
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
  ((((ssPost tx storage observableSlots ∅).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1)).insert
          (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1)

/-- Both concrete SimpleStorage selector tags fit in a `UInt256`. -/
private theorem simpleStorageHitCases_tagsRange
    {cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)}
    {storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt}
    (hCases : cases' = [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')]) :
    ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
  intro tag body hMem
  rw [hCases] at hMem
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hMem
  rcases hMem with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

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
      0x6057361d = tx.functionSelector % Constants.selectorModulus)
    (hCases : cases' = [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')])
    (hBody : ∀ pre suffix, cases' = pre ++ (0x6057361d, storeBody') :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block storeBody')
        (some ssNC)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) = .error err)
    (hReduction :
      Backends.Native.contractDispatcherExecResult
          (fuel + cases'.length + 20)
          ssNC
          (ssInit tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block [Backends.lowerNativeSwitchBlock
            ssSelExpr
            switchId cases' [Backends.Native.nativeRevertZeroZeroStmt]])
          (some ssNC)
          ((ssPost tx storage observableSlots ∅).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1))) :
    Backends.Native.contractDispatcherExecResult
        (fuel + cases'.length + 20)
        ssNC
        (ssInit tx storage observableSlots) = .error err := by
  rw [hReduction]
  exact (Backends.Native.exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_error_projectResult_eq
    fuel 0x6057361d switchId 0x6057361d cases' [Backends.Native.nativeRevertZeroZeroStmt] storeBody'
    ssNC tx storage [] observableSlots err
    (Backends.Native.projectResult tx storage [] (.error err)) hSelector
    (by rw [hCases]; rfl) (by norm_num [EvmYul.UInt256.size])
    (simpleStorageHitCases_tagsRange hCases) (by convert hBody using 1; rfl) rfl).1

private def simpleStorageLoweredHitCasesShape
    (reservedNames : List String) (n0 midN : Nat)
    (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt) : Prop :=
  Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1)
      simpleStorageBuildSwitchSourceCases =
    .ok ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')], midN)

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

private theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_via_reduction
    (fuel switchId : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector :
      0x2e64cec1 = tx.functionSelector % Constants.selectorModulus)
    (hCases : cases' = [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')])
    (hBody : ∀ pre suffix, cases' = pre ++ (0x2e64cec1, retrieveBody') :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block retrieveBody')
        (some ssNC)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) = .error err)
    (hReduction :
      Backends.Native.contractDispatcherExecResult
          (fuel + cases'.length + 20)
          ssNC
          (ssInit tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block [Backends.lowerNativeSwitchBlock
            ssSelExpr
            switchId cases' [Backends.Native.nativeRevertZeroZeroStmt]])
          (some ssNC)
          ((ssPost tx storage observableSlots ∅).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1))) :
    Backends.Native.contractDispatcherExecResult
        (fuel + cases'.length + 20)
        ssNC
        (ssInit tx storage observableSlots) = .error err := by
  rw [hReduction]
  exact (Backends.Native.exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_error_projectResult_eq
    fuel 0x2e64cec1 switchId 0x2e64cec1 cases' [Backends.Native.nativeRevertZeroZeroStmt]
    retrieveBody'
    ssNC tx storage [] observableSlots err
    (Backends.Native.projectResult tx storage [] (.error err)) hSelector
    (by rw [hCases]; rfl) (by norm_num [EvmYul.UInt256.size])
    (simpleStorageHitCases_tagsRange hCases) (by convert hBody using 1; rfl) rfl).1

private noncomputable def simpleStorageNativeDispatcherFuel : Nat :=
  sizeOf ssRuntime

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
    (hSelectorRange : tx.functionSelector % Constants.selectorModulus
        < EvmYul.UInt256.size)
    (hSelMissStore : tx.functionSelector % Constants.selectorModulus
        ≠ 0x6057361d)
    (hSelMissRetrieve : tx.functionSelector % Constants.selectorModulus
        ≠ 0x2e64cec1)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    Backends.Native.contractDispatcherExecResult
        simpleStorageNativeDispatcherFuel
        ssNC
        (ssInit tx storage
          observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  have hReshape : simpleStorageNativeDispatcherFuel =
      (simpleStorageNativeDispatcherFuel - 22) + 22 :=
    (Nat.sub_add_cancel simpleStorageNativeDispatcherFuel_ge_22).symm
  rw [hReshape]
  exact simpleStorageNativeContract_dispatcherExec_selectorMiss_revert
    (simpleStorageNativeDispatcherFuel - 22)
    (tx.functionSelector % Constants.selectorModulus)
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

/-- The IR retrieve body `mstore(0, sload(0)); return(0, 32)`. -/
private abbrev simpleStorageRetrieveIRBody : List Yul.YulStmt :=
  [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
      [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
   Yul.YulStmt.exprStmt (Yul.YulExpr.call "return"
      [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])]

/-- Closed-form evaluation of the IR retrieve body for any fuel `≥ 3`. -/
private theorem execIRStmts_simpleStorageRetrieveIRBody
    (n : Nat) (s : IRState) (hn : 2 ≤ n) :
    execIRStmts (n + 1) s simpleStorageRetrieveIRBody =
      .return ((s.storage (IRStorageSlot.ofNat 0)).toNat)
        (s.writePhysicalMemoryValue 0 (s.storage (IRStorageSlot.ofNat 0)).toNat) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hword : (s.writePhysicalMemoryValue 0 (s.storage (IRStorageSlot.ofNat 0)).toNat).memory 0 =
      (s.storage (IRStorageSlot.ofNat 0)).toNat := by
    rw [IRState.writePhysicalMemoryValue_at, Verity.Core.Uint256.val_ofNat]
    exact Nat.mod_eq_of_lt (IRStorageWord.toNat_lt_size _)
  -- Fuel `k + 2 + 1 = k + 3` is `Nat.succ (Nat.succ (Nat.succ k))`, allowing
  -- both the outer `execIRStmts` and the inner `execIRStmt` to step.
  simp +decide only [execIRStmts, execIRStmt, evalIRExpr,
    evalIRCall_sload_singleton, Compiler.Proofs.abstractLoadStorageOrMapping,
    Option.bind_some, ↓reduceIte, Verity.Core.Uint256.val_ofNat, Nat.zero_mod, hword]

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
  -- The retrieve body has at least 2 statements, so `sizeOf body ≥ 2` by
  -- direct computation on the auto-derived size measure.
  have hsize : 2 ≤ sizeOf simpleStorageRetrieveIRBody := by
    decide
  unfold interpretIR
  simp only [simpleStorageIRContract, List.find?, hstore, hretrieve,
    List.length_nil, Nat.zero_le, ↓reduceDIte]
  -- Now goal involves `execIRFunction retrieveFn tx.args state'`.
  unfold execIRFunction
  simp only [List.zip_nil_left, List.foldl_nil]
  -- Goal: `match execIRStmts (sizeOf body + 1) state' body with ... = ...`.
  rw [execIRStmts_simpleStorageRetrieveIRBody _ _ hsize]
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

/-- The concrete lowered SimpleStorage selector cases, `store` before
`retrieve`. -/
private abbrev simpleStorageLoweredHitCases : List (Nat × List EvmYul.Yul.Ast.Stmt) :=
  [(0x6057361d, simpleStorageLoweredStoreCaseBody),
   (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)]

/-- The chained-insert varStore of the dispatcher hit-body input state. -/
private def simpleStorageDispatcherHitStore (switchId : Nat) (tx : YulTransaction) :
    EvmYul.Yul.VarStore :=
  ((((∅ : EvmYul.Yul.VarStore).insert "__has_selector"
          (EvmYul.UInt256.ofNat 1)).insert
        (Backends.nativeSwitchDiscrTempName switchId)
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Constants.selectorModulus))).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 0)).insert
    (Backends.nativeSwitchMatchedTempName switchId)
    (EvmYul.UInt256.ofNat 1)

/-- A zero (mod `2^256`) message value surfaces as a zero native `weiValue`. -/
private theorem nativeSwitchPostInitFreeMemorySharedState_weiValue_zero
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) :
    (Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).executionEnv.weiValue =
      (⟨0⟩ : EvmYul.Literal) := by
  rw [nativeSwitchPostInitFreeMemorySharedState_weiValue]
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  simpa [Backends.StateBridge.natToUInt256,
    EvmYul.UInt256.ofNat, Fin.ofNat] using hMsgValue

/-- In the concrete case list, the `store` case can only be split off with an
empty prefix. -/
private theorem simpleStorageLoweredHitCases_store_decomp
    {pre suffix : List (Nat × List EvmYul.Yul.Ast.Stmt)}
    (h : simpleStorageLoweredHitCases =
      pre ++ (0x6057361d, simpleStorageLoweredStoreCaseBody) :: suffix) :
    pre = [] ∧ suffix = [(0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] := by
  rcases pre with _ | ⟨_, _ | ⟨_, _⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h.2.symm⟩
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq] at h
    exact absurd h.2.1.1 (by decide)
  · simp at h

/-- In the concrete case list, the `retrieve` case can only be split off after
the single `store` case. -/
private theorem simpleStorageLoweredHitCases_retrieve_decomp
    {pre suffix : List (Nat × List EvmYul.Yul.Ast.Stmt)}
    (h : simpleStorageLoweredHitCases =
      pre ++ (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody) :: suffix) :
    suffix = [] := by
  rcases pre with _ | ⟨_, _ | ⟨_, _⟩⟩
  · simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at h
    exact absurd h.1.1 (by decide)
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact h.2.2.symm
  · simp at h

/-- Opening the source-lowered dispatcher reduction and pinning the lowered
cases to `simpleStorageLoweredHitCases` at dispatcher fuel `g + 26`. -/
private theorem simpleStorageNativeContract_dispatcherExec_hitCases_reduction
    (g : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ switchId,
      Backends.Native.contractDispatcherExecResult
          ((g + 4) + simpleStorageLoweredHitCases.length + 20)
          ssNC
          (ssInit tx storage observableSlots) =
        EvmYul.Yul.exec ((g + 4) + simpleStorageLoweredHitCases.length + 13)
          (.Block [Backends.lowerNativeSwitchBlock
            ssSelExpr
            switchId simpleStorageLoweredHitCases [Backends.Native.nativeRevertZeroZeroStmt]])
          (some ssNC)
          ((ssPost tx storage observableSlots ∅).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1)) := by
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
  refine ⟨Backends.freshNativeSwitchId reservedNames n0, ?_⟩
  rw [show (g + 4) + simpleStorageLoweredHitCases.length + 20 = g + 11 + 15 from rfl,
    show (g + 4) + simpleStorageLoweredHitCases.length + 13 = g + 11 + 8 from rfl]
  exact hExec

/-- `simpleStorageNativeDispatcherFuel` written as `(g + 4) + |cases| + 20`. -/
private theorem simpleStorageNativeDispatcherFuel_eq_hitCases :
    simpleStorageNativeDispatcherFuel =
      ((simpleStorageNativeDispatcherFuel - 26) + 4) +
        simpleStorageLoweredHitCases.length + 20 := by
  have := simpleStorageNativeDispatcherFuel_ge_26
  simp only [List.length_cons, List.length_nil]
  omega

/-- Generic store-hit dispatcher endpoint at `simpleStorageNativeDispatcherFuel`:
any switch-id-indexed error produced by the lowered store body is the
dispatcher result. -/
private theorem simpleStorageNativeContract_dispatcherExec_storeHit_atFuel_of_body
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (errOf : Nat → EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : ∀ g switchId,
      EvmYul.Yul.exec (g + 13) (.Block simpleStorageLoweredStoreCaseBody)
        (some ssNC)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage observableSlots) =
        .error (errOf switchId)) :
    ∃ switchId,
      Backends.Native.contractDispatcherExecResult
          simpleStorageNativeDispatcherFuel
          ssNC
          (ssInit tx storage
            observableSlots) =
        .error (errOf switchId) := by
  set g := simpleStorageNativeDispatcherFuel - 26
  obtain ⟨switchId, hReduction⟩ :=
    simpleStorageNativeContract_dispatcherExec_hitCases_reduction g tx storage
      observableSlots hNoWrap
  refine ⟨switchId, ?_⟩
  rw [simpleStorageNativeDispatcherFuel_eq_hitCases]
  refine simpleStorageNativeContract_dispatcherExec_storeHit_error_via_reduction
    (g + 4) switchId simpleStorageLoweredHitCases _ _ tx storage observableSlots
    (errOf switchId) hSelector rfl ?_ hReduction
  intro pre suffix hDecomp
  obtain ⟨-, rfl⟩ := simpleStorageLoweredHitCases_store_decomp hDecomp
  exact hBody g switchId

/-- Generic retrieve-hit dispatcher endpoint at
`simpleStorageNativeDispatcherFuel`, the dual of
`_storeHit_atFuel_of_body`. -/
private theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_atFuel_of_body
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (errOf : Nat → EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : ∀ g switchId,
      EvmYul.Yul.exec (g + 12) (.Block simpleStorageLoweredRetrieveCaseBody)
        (some ssNC)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage observableSlots) =
        .error (errOf switchId)) :
    ∃ switchId,
      Backends.Native.contractDispatcherExecResult
          simpleStorageNativeDispatcherFuel
          ssNC
          (ssInit tx storage
            observableSlots) =
        .error (errOf switchId) := by
  set g := simpleStorageNativeDispatcherFuel - 26
  obtain ⟨switchId, hReduction⟩ :=
    simpleStorageNativeContract_dispatcherExec_hitCases_reduction g tx storage
      observableSlots hNoWrap
  refine ⟨switchId, ?_⟩
  rw [simpleStorageNativeDispatcherFuel_eq_hitCases]
  refine simpleStorageNativeContract_dispatcherExec_retrieveHit_error_via_reduction
    (g + 4) switchId simpleStorageLoweredHitCases _ _ tx storage observableSlots
    (errOf switchId) hSelector rfl ?_ hReduction
  intro pre suffix hDecomp
  obtain rfl := simpleStorageLoweredHitCases_retrieve_decomp hDecomp
  exact hBody g switchId

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
    (hSelector : 0x2e64cec1 = tx.functionSelector % Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) :
    let shared :=
      ssShared tx storage observableSlots
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
      Backends.Native.contractDispatcherExecResult
          simpleStorageNativeDispatcherFuel
          ssNC
          (ssInit tx storage
            observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store) ⟨1⟩) := by
  intro shared p shared1 shared2 shared3
  have hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size := by
    rw [nativeSwitchPostInitFreeMemorySharedState_calldata_size]
    exact hNoWrap
  have hGe : 4 ≤ shared.executionEnv.calldata.size := by
    rw [nativeSwitchPostInitFreeMemorySharedState_calldata_size]
    exact Nat.le_add_right 4 _
  obtain ⟨switchId, h⟩ :=
    simpleStorageNativeContract_dispatcherExec_retrieveHit_atFuel_of_body
      tx storage observableSlots
      (fun switchId => EvmYul.Yul.Exception.YulHalt
        (.Ok shared3 (simpleStorageDispatcherHitStore switchId tx)) ⟨1⟩)
      hSelector hNoWrap
      (fun g switchId => exec_block_simpleStorageLoweredRetrieveCaseBody_halt g _ shared
        (simpleStorageDispatcherHitStore switchId tx)
        (nativeSwitchPostInitFreeMemorySharedState_weiValue_zero _ tx storage
          observableSlots hMsgValue) hSize hGe)
  exact ⟨_, h⟩

/-- Native dispatcher exec at exactly `simpleStorageNativeDispatcherFuel`
reduces to the `STOP` halt for the store-hit class when calldata supplies the
setter argument. -/
private theorem simpleStorageNativeContract_dispatcherExec_storeHit_halt_atFuel
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest)
    (hSelector : 0x6057361d = tx.functionSelector % Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) :
    ∃ store_body haltState,
      Backends.Native.contractDispatcherExecResult
          simpleStorageNativeDispatcherFuel
          ssNC
          (ssInit tx storage
            observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState ⟨0⟩) ∧
      haltState =
        let initialWithStore : EvmYul.Yul.State :=
          .Ok (ssShared tx storage
            observableSlots) store_body
        let withValue := initialWithStore.insert "value"
          (Backends.StateBridge.natToUInt256 arg)
        withValue.setState
          (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
            (Backends.StateBridge.natToUInt256 arg)) := by
  obtain ⟨hSize, hGe⟩ := nativeSwitchPostInitFreeMemorySharedState_calldata_bounds_36
    ssNC tx storage observableSlots
    arg rest hArgs hNoWrap
  obtain ⟨switchId, h⟩ :=
    simpleStorageNativeContract_dispatcherExec_storeHit_atFuel_of_body
      tx storage observableSlots _ hSelector hNoWrap
      (fun g switchId => exec_block_simpleStorageLoweredStoreCaseBody_halt g _
        (ssShared tx storage observableSlots)
        tx storage observableSlots (simpleStorageDispatcherHitStore switchId tx) arg rest hArgs
        (nativeSwitchPostInitFreeMemorySharedState_perm _ tx storage observableSlots)
        (nativeSwitchPostInitFreeMemorySharedState_calldataload4
          _ tx storage observableSlots arg rest hArgs)
        (nativeSwitchPostInitFreeMemorySharedState_weiValue_zero _ tx storage
          observableSlots hMsgValue) hSize hGe)
  exact ⟨_, _, h, rfl⟩

/-- Native dispatcher exec at exactly `simpleStorageNativeDispatcherFuel`
reverts for the store-hit class when calldata contains no setter argument. -/
private theorem simpleStorageNativeContract_dispatcherExec_storeHit_short_revert_atFuel
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hArgs : tx.args = [])
    (hSelector : 0x6057361d = tx.functionSelector % Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) :
    Backends.Native.contractDispatcherExecResult
        simpleStorageNativeDispatcherFuel
        ssNC
        (ssInit tx storage
          observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  have hSizeEq :
      (ssShared tx storage
        observableSlots).executionEnv.calldata.size = 4 := by
    rw [nativeSwitchPostInitFreeMemorySharedState_calldata_size]
    simp [hArgs]
  obtain ⟨_, h⟩ :=
    simpleStorageNativeContract_dispatcherExec_storeHit_atFuel_of_body
      tx storage observableSlots (fun _ => EvmYul.Yul.Exception.Revert) hSelector hNoWrap
      (fun g switchId => exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error
        (g + 11) _ _ _
        (exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error
          (g + 4) _ _ (simpleStorageDispatcherHitStore switchId tx) _
          (nativeSwitchPostInitFreeMemorySharedState_weiValue_zero _ tx storage
            observableSlots hMsgValue)
          (exec_block_simpleStorageLoweredStoreCaseBodyTail2_short_revert g _ _ _ hSizeEq)))
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
    (Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage slots).toState =
      (Backends.Native.initialState
        contract tx storage slots).sharedState.toState := by
  rfl

private theorem projectStorageFromState_eq_of_accountMap_eq
    (tx : YulTransaction) (left right : EvmYul.Yul.State)
    (h :
      left.sharedState.accountMap =
        right.sharedState.accountMap) :
    Backends.Native.projectStorageFromState tx left =
      Backends.Native.projectStorageFromState tx right := by
  unfold Backends.Native.projectStorageFromState
  unfold Backends.StateBridge.extractStorage
  rw [h]

private theorem projectStorageFromState_insert_sstore_eq_of_toState_eq
    (tx : YulTransaction)
    (leftShared rightShared : EvmYul.SharedState .Yul)
    (leftStore rightStore : EvmYul.Yul.VarStore)
    (name : String) (value slot stored : EvmYul.UInt256)
    (hState : leftShared.toState = rightShared.toState) :
    Backends.Native.projectStorageFromState tx
        (((EvmYul.Yul.State.Ok leftShared leftStore).insert name value).setState
          (((EvmYul.Yul.State.Ok leftShared leftStore).insert name value).toState.sstore
            slot stored)) =
      Backends.Native.projectStorageFromState tx
        (((EvmYul.Yul.State.Ok rightShared rightStore).insert name value).setState
          (((EvmYul.Yul.State.Ok rightShared rightStore).insert name value).toState.sstore
            slot stored)) := by
  apply projectStorageFromState_eq_of_accountMap_eq
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.insert,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState]
  rw [hState]

/-- Projected lookup of a materialized slot other than slot zero is unchanged
by a write to slot zero. -/
private theorem simpleStorage_projectStorage_lookup_ne_zero
    (storage : IRStorageSlot → IRStorageWord) (slots : List Nat) (arg slot : Nat)
    (hSlot : slot ∈ slots)
    (hKey : compare (EvmYul.UInt256.ofNat slot) (EvmYul.UInt256.ofNat 0) ≠ Ordering.eq) :
    (match (Backends.StateBridge.projectStorage
        storage slots)[EvmYul.UInt256.ofNat slot]? with
      | some val => val
      | none => 0) =
      Compiler.Proofs.abstractStoreStorageOrMapping storage 0 arg (IRStorageSlot.ofNat slot) := by
  have hLookup :=
    Backends.StateBridge.storageLookup_projectStorage_projected
      storage slots slot hSlot
  have hSlotNeUInt : EvmYul.UInt256.ofNat slot ≠ EvmYul.UInt256.ofNat 0 := by
    intro hEq
    apply hKey
    rw [hEq]
    exact Std.ReflCmp.compare_self
  unfold Backends.StateBridge.storageLookup at hLookup
  simp only [Compiler.Proofs.abstractStoreStorageOrMapping,
    IRStorageSlot.ofNat, if_neg hSlotNeUInt]
  unfold Compiler.Proofs.IRGeneration.IRStorageWord
  have hZero : (0 : EvmYul.UInt256) =
      (Inhabited.default : EvmYul.UInt256) := by rfl
  rw [hZero]
  convert hLookup using 1 <;> rfl

/-- A `UInt256` that compares equal to the default word is the zero word. -/
private theorem simpleStorage_uint256_eq_zero_of_beq_default (w : EvmYul.UInt256)
    (h : (w == (Inhabited.default : EvmYul.UInt256)) = true) :
    w = (⟨0⟩ : EvmYul.UInt256) := by
  cases w with
  | mk v =>
      change (v == (0 : Fin EvmYul.UInt256.size)) = true at h
      have hv : v = (0 : Fin EvmYul.UInt256.size) := of_decide_eq_true h
      subst hv
      rfl

/-- Zero-write case of `projectStorageFromState_storeHit_initialState_materialized`:
the native map erases slot zero, which still projects to the IR zero word. -/
private theorem simpleStorage_projectStorage_erase_zero_lookup
    (storage : IRStorageSlot → IRStorageWord) (slots : List Nat) (arg slot : Nat)
    (hSlot : slot ∈ slots)
    (hValueZero :
      (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) = true) :
    (match (Std.TreeMap.erase
        (Backends.StateBridge.projectStorage storage slots)
        (EvmYul.UInt256.ofNat 0))[EvmYul.UInt256.ofNat slot]? with
      | some val => val
      | none => 0) =
      Compiler.Proofs.abstractStoreStorageOrMapping storage 0 arg (IRStorageSlot.ofNat slot) := by
  have hArgZeroUInt := simpleStorage_uint256_eq_zero_of_beq_default _ hValueZero
  by_cases hKey :
      compare (EvmYul.UInt256.ofNat slot) (EvmYul.UInt256.ofNat 0) = Ordering.eq
  · have hUInt : EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 :=
      Backends.StateBridge.UInt256_eq_of_compare_eq hKey
    have hErase :
        (Std.TreeMap.erase
          (Backends.StateBridge.projectStorage
            storage slots)
          (EvmYul.UInt256.ofNat 0))[EvmYul.UInt256.ofNat slot]? = none := by
      simp [hUInt]
    rw [hErase]
    simp only [Compiler.Proofs.abstractStoreStorageOrMapping,
      Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, IRStorageSlot.ofNat, hUInt]
    simp only [if_true]
    rw [hArgZeroUInt]
    rfl
  · rw [simpleStorage_storage_get?_erase_of_ne _ _ _ hKey]
    exact simpleStorage_projectStorage_lookup_ne_zero storage slots arg slot hSlot hKey

/-- Nonzero-write case of
`projectStorageFromState_storeHit_initialState_materialized`. -/
private theorem simpleStorage_projectStorage_insert_zero_lookup
    (storage : IRStorageSlot → IRStorageWord) (slots : List Nat) (arg slot : Nat)
    (hSlot : slot ∈ slots) :
    (match (Std.TreeMap.insert
        (Backends.StateBridge.projectStorage storage slots)
        (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat arg))[EvmYul.UInt256.ofNat slot]? with
      | some val => val
      | none => 0) =
      Compiler.Proofs.abstractStoreStorageOrMapping storage 0 arg (IRStorageSlot.ofNat slot) := by
  by_cases hKey :
      compare (EvmYul.UInt256.ofNat slot) (EvmYul.UInt256.ofNat 0) = Ordering.eq
  · have hUInt : EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 :=
      Backends.StateBridge.UInt256_eq_of_compare_eq hKey
    rw [simpleStorage_storage_get?_insert_of_eq _ _ _ _ hKey]
    simp [Compiler.Proofs.abstractStoreStorageOrMapping,
      Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, IRStorageSlot.ofNat, hUInt]
  · rw [simpleStorage_storage_get?_insert_of_ne _ _ _ _ hKey]
    exact simpleStorage_projectStorage_lookup_ne_zero storage slots arg slot hSlot hKey

private theorem projectStorageFromState_storeHit_initialState_materialized
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (store : EvmYul.Yul.VarStore)
    (arg slot : Nat)
    (hSlot : slot ∈ slots) :
    let initialWithStore : EvmYul.Yul.State :=
      .Ok (Backends.Native.initialState
        contract tx storage slots).sharedState store
    let withValue := initialWithStore.insert "value"
      (Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Backends.StateBridge.natToUInt256 arg))
    Backends.Native.projectStorageFromState tx
        finalState (IRStorageSlot.ofNat slot) =
      (Compiler.Proofs.abstractStoreStorageOrMapping storage 0 arg)
        (IRStorageSlot.ofNat slot) := by
  intro initialWithStore withValue finalState
  simp only [Backends.Native.projectStorageFromState,
    Backends.StateBridge.extractStorage,
    finalState, withValue, initialWithStore,
    EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
    EvmYul.Yul.State.toState, EvmYul.Yul.State.insert,
    EvmYul.State.sstore, EvmYul.State.lookupAccount,
    EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
    Backends.Native.initialState,
    Backends.StateBridge.toSharedState,
    YulState.initial,
    Backends.StateBridge.natToUInt256]
  simp only [Option.option, Std.TreeMap.get?_eq_getElem?,
    Std.TreeMap.getElem?_insert_self]
  by_cases hValueZero :
      (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) = true
  · rw [simpleStorage_account_updateStorage_storage_of_zero _ _ _ hValueZero]
    simp only [IRStorageSlot.toUInt256, IRStorageSlot.ofNat]
    exact simpleStorage_projectStorage_erase_zero_lookup storage slots arg slot hSlot hValueZero
  · have hValueNonzero :
        (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) = false := by
      simpa using hValueZero
    rw [simpleStorage_account_updateStorage_storage_of_nonzero _ _ _ hValueNonzero]
    simp only [IRStorageSlot.toUInt256, IRStorageSlot.ofNat]
    exact simpleStorage_projectStorage_insert_zero_lookup storage slots arg slot hSlot

private theorem projectStorageFromState_storeHit_postInit_materialized
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (store : EvmYul.Yul.VarStore)
    (arg slot : Nat) (hSlot : slot ∈ slots) :
    let initialWithStore : EvmYul.Yul.State := .Ok
      (Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        contract tx storage slots) store
    let withValue := initialWithStore.insert "value"
      (Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Backends.StateBridge.natToUInt256 arg))
    Backends.Native.projectStorageFromState tx
        finalState (IRStorageSlot.ofNat slot) =
      (Compiler.Proofs.abstractStoreStorageOrMapping storage 0 arg)
        (IRStorageSlot.ofNat slot) := by
  intro initialWithStore withValue finalState
  have hInitial :=
    projectStorageFromState_storeHit_initialState_materialized
      contract tx storage slots store arg slot hSlot
  have hTransport :=
    projectStorageFromState_insert_sstore_eq_of_toState_eq tx
      (Backends.Native.nativeSwitchPostInitFreeMemorySharedState
        contract tx storage slots)
      (Backends.Native.initialState
        contract tx storage slots).sharedState
      store store "value"
      (Backends.StateBridge.natToUInt256 arg)
      (EvmYul.UInt256.ofNat 0)
      (Backends.StateBridge.natToUInt256 arg)
      (nativeSwitchPostInitFreeMemorySharedState_toState contract tx storage slots)
  rw [hTransport]
  exact hInitial

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
      -ByteArray.size_data, ByteArray.size]
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
    -ByteArray.size_data, ByteArray.size]
  norm_num
  omega

private theorem nativeSwitchPostInitFreeMemorySharedState_memory_size_ge_32
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    32 ≤ (Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage observableSlots).memory.size := by
  simp [Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    Backends.Native.initialState,
    Backends.StateBridge.toSharedState,
    Backends.StateBridge.mkBlockHeader,
    Constants.freeMemoryPointer, YulState.initial,
    EvmYul.Yul.State.sharedState, EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes]
  exact byteArray_write_empty_64_32_size_ge_32
    (EvmYul.UInt256.ofNat 128).toByteArray
    (Backends.Native.uint256_toByteArray_size
      (EvmYul.UInt256.ofNat 128))

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
    (Backends.Native.uint256_toByteArray_size value)
    hMemorySize

/-- Native `mstore(0, value); return(0, 32)` on a shared state with at least
32 bytes of memory halts returning exactly `value`. -/
private theorem projectHaltReturn_mstore0_return32
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256) (hMemorySize : 32 ≤ shared.memory.size) :
    let shared1 : EvmYul.SharedState .Yul :=
      { shared with
        toMachineState := shared.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    Backends.Native.projectHaltReturn
        (EvmYul.Yul.State.Ok shared2 store) ⟨1⟩ = some value.toNat := by
  intro shared1 shared2
  have hSize :
      (EvmYul.Yul.State.Ok shared2 store).sharedState.H_return.size = 32 := by
    have h := Backends.Native.mstore0_then_return32_hReturn_size
      shared store value
    simpa [shared2, shared1, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.sharedState] using h
  have hH_return :
      (EvmYul.Yul.State.Ok shared2 store).sharedState.H_return = value.toByteArray := by
    have h := mstore0_then_return32_hReturn_eq_toByteArray shared store value hMemorySize
    simpa [shared2, shared1, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.sharedState] using h
  have hHaltNotZero : (⟨1⟩ : EvmYul.Yul.Ast.Literal) ≠ ⟨0⟩ := by
    intro h
    norm_num [EvmYul.UInt256.size] at h
  rw [Backends.Native.projectHaltReturn_32ByteReturn
    (EvmYul.Yul.State.Ok shared2 store) ⟨1⟩ hHaltNotZero hSize]
  rw [hH_return,
    Backends.Native.byteArrayWord_uint256_toByteArray]

/-- Storage projection from a native shared state that still carries the
initial account map agrees with IR storage on every materialized slot. -/
private theorem projectStorageFromState_of_initial_accountMap
    (nativeContract : EvmYul.Yul.Ast.YulContract) (yulTx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (slots : List Nat)
    (s : EvmYul.SharedState .Yul) (st : EvmYul.Yul.VarStore) (slot : Nat)
    (hslot : slot ∈ slots)
    (hAccountMap :
      s.accountMap =
        (Backends.Native.initialState
          nativeContract yulTx storage slots).sharedState.accountMap) :
    Backends.Native.projectStorageFromState
        yulTx (EvmYul.Yul.State.Ok s st) (IRStorageSlot.ofNat slot) =
      storage (IRStorageSlot.ofNat slot) := by
  have hNative :=
    Backends.Native.initialState_materializedStorageSlot
      nativeContract yulTx storage slots slot hslot
  simpa [Backends.Native.projectStorageFromState,
    Backends.StateBridge.extractStorage,
    EvmYul.Yul.State.sharedState, hAccountMap] using hNative

/-- Observable slots are always materialized. -/
private theorem mem_materializedStorageSlots_of_mem
    (code : List Yul.YulStmt) (observableSlots : List Nat) (slot : Nat)
    (hslot : slot ∈ observableSlots) :
    slot ∈ Backends.Native.materializedStorageSlots
      code observableSlots := by
  simp [Backends.Native.materializedStorageSlots, hslot]

/-- Generic observable agreement for a native `mstore(0, w); return(0, 32)`
halt from a shared state that keeps the initial account map and emitted no
logs, against an IR result returning `rv = w.toNat` with storage and events
unchanged. -/
private theorem nativeResultsMatchOn_mstore0_return32_of_accountMap
    (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (yulTx : YulTransaction) (state : IRState) (slots : List Nat)
    (hSlots : ∀ slot ∈ observableSlots, slot ∈ slots)
    (s : EvmYul.SharedState .Yul) (st : EvmYul.Yul.VarStore)
    (w : EvmYul.UInt256) (rv : Nat) (hrv : w.toNat = rv)
    (hMemorySize : 32 ≤ s.memory.size)
    (hAccountMap :
      s.accountMap =
        (Backends.Native.initialState
          nativeContract yulTx state.storage slots).sharedState.accountMap)
    (hLogs :
      Backends.Native.projectLogsFromState
        (EvmYul.Yul.State.Ok s st) = []) :
    let shared1 : EvmYul.SharedState .Yul :=
      { s with toMachineState := s.toMachineState.mstore (EvmYul.UInt256.ofNat 0) w }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    nativeResultsMatchOn observableSlots
      { success := true
        returnValue := some rv
        finalStorage := state.storage
        finalMappings := Compiler.Proofs.storageAsMappings state.storage
        events := state.events }
      (.ok
        (Backends.Native.projectResult
          yulTx state.storage state.events
          (.error (EvmYul.Yul.Exception.YulHalt
            (EvmYul.Yul.State.Ok shared2 st) ⟨1⟩)))) := by
  intro shared1 shared2
  have hReturnValue :
      Backends.Native.projectHaltReturn
        (EvmYul.Yul.State.Ok shared2 st) ⟨1⟩ = some w.toNat :=
    projectHaltReturn_mstore0_return32 s st w hMemorySize
  simp only [Backends.Native.projectResult, hReturnValue]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [hrv]
  · intro slot hslot
    exact (projectStorageFromState_of_initial_accountMap nativeContract yulTx
      state.storage slots shared2 st slot (hSlots slot hslot) hAccountMap).symm
  · have hLogs2 :
        Backends.Native.projectLogsFromState
          (EvmYul.Yul.State.Ok shared2 st) = [] := hLogs
    rw [hLogs2, List.append_nil]

/-- `sload(0)` on the post-init dispatcher shared state reads IR slot zero. -/
private theorem nativeSwitchPostInitFreeMemorySharedState_sload0_value
    (irContract : IRContract) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (yulTx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    let slots := Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode irContract) observableSlots
    ((Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      nativeContract yulTx storage slots).sload (EvmYul.UInt256.ofNat 0)).2 =
      storage (IRStorageSlot.ofNat 0) := by
  intro slots
  have hload :=
    Backends.Native.initialState_sload_materializedSlot_value
      nativeContract yulTx storage slots 0
      (by simp [slots, Backends.Native.materializedStorageSlots])
  have hsload := congrArg
    (fun s : EvmYul.State .Yul => (s.sload (EvmYul.UInt256.ofNat 0)).2)
    (nativeSwitchPostInitFreeMemorySharedState_toState nativeContract yulTx storage slots)
  simpa using hsload.trans hload

/-- `sload(0)` on the post-init dispatcher shared state emits no logs. -/
private theorem projectLogsFromState_postInit_sload0
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (slots : List Nat)
    (st : EvmYul.Yul.VarStore) :
    let shared := Backends.Native.nativeSwitchPostInitFreeMemorySharedState
      contract tx storage slots
    Backends.Native.projectLogsFromState
      (EvmYul.Yul.State.Ok
        { shared with toState := (shared.sload (EvmYul.UInt256.ofNat 0)).1 } st) = [] := by
  intro shared
  simp [Backends.Native.projectLogsFromState, shared,
    Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
    Backends.Native.initialState,
    Backends.StateBridge.toSharedState,
    YulState.initial, EvmYul.State.sload, EvmYul.State.addAccessedStorageKey,
    EvmYul.Substate.addAccessedStorageKey, EvmYul.Yul.State.sharedState]
  rfl

/-- `nativeResultsMatchOn_mstore0_return32_of_accountMap` for the retrieve
payload `mstore(0, sload(0)); return(0, 32)` from the generated dispatcher
post-init shared state. -/
private theorem nativeResultsMatchOn_mstore0_sload0_return32_postInit
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (st : EvmYul.Yul.VarStore) :
    let yulTx := YulTransaction.ofIR tx
    let slots := Backends.Native.materializedStorageSlots (Compiler.runtimeCode irContract) observableSlots
    let shared := Backends.Native.nativeSwitchPostInitFreeMemorySharedState nativeContract yulTx state.storage slots
    let p := shared.sload (EvmYul.UInt256.ofNat 0)
    let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with toMachineState := shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
    let shared3 : EvmYul.SharedState .Yul :=
      { shared2 with toMachineState := shared2.toMachineState.evmReturn (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    nativeResultsMatchOn observableSlots
      { success := true, returnValue := some ((state.storage (IRStorageSlot.ofNat 0)).toNat),
        finalStorage := state.storage, finalMappings := Compiler.Proofs.storageAsMappings state.storage,
        events := state.events }
      (.ok (Backends.Native.projectResult yulTx state.storage state.events
        (.error (EvmYul.Yul.Exception.YulHalt (EvmYul.Yul.State.Ok shared3 st) ⟨1⟩)))) := by
  intro yulTx slots shared p shared1 shared2 shared3
  have hp : p.2 = state.storage (IRStorageSlot.ofNat 0) :=
    nativeSwitchPostInitFreeMemorySharedState_sload0_value irContract nativeContract yulTx
      state.storage observableSlots
  have hAccountMap : shared1.accountMap =
      (Backends.Native.initialState nativeContract yulTx state.storage slots).sharedState.accountMap := by
    simp [shared1, p, shared, EvmYul.State.sload, EvmYul.State.addAccessedStorageKey]
  exact nativeResultsMatchOn_mstore0_return32_of_accountMap observableSlots nativeContract
    yulTx state slots (mem_materializedStorageSlots_of_mem _ observableSlots)
    shared1 st p.2 ((state.storage (IRStorageSlot.ofNat 0)).toNat)
    (by simp [hp, Compiler.Proofs.IRGeneration.IRStorageWord.toNat])
    (by simpa [shared1] using nativeSwitchPostInitFreeMemorySharedState_memory_size_ge_32 _ _ _ _)
    hAccountMap (projectLogsFromState_postInit_sload0 _ _ _ _ _)

set_option maxRecDepth 10000

/-- Named SimpleStorage native dispatcher direct-match obligation.

The lowered native dispatcher result is compared with `interpretIR` directly
instead of with the EVMYulLean fuel wrapper. -/
private def simpleStorageNativeCallDispatcherMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    ssNC

/-! ### Per-case sub-bridges for the SimpleStorage native dispatcher. -/

/-- Direct-match per-case sub-bridge for the `retrieve()` selector hit. -/
private def simpleStorageNativeRetrieveHitMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  tx.functionSelector % Constants.selectorModulus = 0x2e64cec1 →
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    ssNC

/-- Direct-match per-case sub-bridge for the `store(uint256)` selector hit. -/
private def simpleStorageNativeStoreHitMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  tx.functionSelector % Constants.selectorModulus = 0x6057361d →
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    ssNC

/-- Direct-match per-case sub-bridge for the selector-miss revert arm. -/
private def simpleStorageNativeSelectorMissMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  tx.functionSelector % Constants.selectorModulus ≠ 0x2e64cec1 →
  tx.functionSelector % Constants.selectorModulus ≠ 0x6057361d →
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    ssNC

/-- Both SimpleStorage functions are non-payable, so dispatch-guard safety
forces a zero (mod `2^256`) message value. -/
private theorem simpleStorage_msgValue_mod_zero_of_dispatchGuardSafe (tx : IRTransaction)
    (hdispatchGuardSafe : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      DispatchGuardsSafe fn tx) :
    tx.msgValue % EvmYul.UInt256.size = 0 := by
  have hguards := hdispatchGuardSafe _
    (List.head_mem (l := simpleStorageIRContract.functions) (by simp [simpleStorageIRContract]))
  rcases hguards with ⟨hValue, _⟩
  rcases hValue with hPayable | hZero
  · simp [simpleStorageIRContract] at hPayable
  · simpa [evmModulus, EvmYul.UInt256.size] using hZero

/-- Store-hit direct match when calldata carries no setter argument: both
sides revert with unchanged storage and events. -/
private theorem simpleStorageNativeStoreHitMatch_short
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hStore : tx.functionSelector % Constants.selectorModulus = 0x6057361d)
    (hSelectorEq : tx.functionSelector = 0x6057361d)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) (hArgs : tx.args = []) :
    nativeDispatcherExecMatchesIRPositive simpleStorageNativeDispatcherFuel
      simpleStorageIRContract tx initialState observableSlots
      ssNC := by
  refine nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
    (err := EvmYul.Yul.Exception.Revert)
    (nativeYul :=
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events })
    ?_ rfl ?_
  · simpa [simpleStorage_runtimeCode_eq_single_dispatcher] using
      (simpleStorageNativeContract_dispatcherExec_storeHit_short_revert_atFuel
        (YulTransaction.ofIR tx) initialState.storage _
        (by simpa [YulTransaction.ofIR] using hArgs)
        (by simpa using hStore.symm)
        (by simpa [YulTransaction.ofIR, evmModulus, Verity.Core.UINT256_MODULUS] using hNoWrap)
        (by simpa [YulTransaction.ofIR] using hMsgValue))
  · rw [interpretIR_simpleStorage_storeHit_short tx initialState hSelectorEq hArgs]
    exact ⟨rfl, rfl, (by intro slot _; rfl), rfl⟩

/-- Observable agreement of the native store halt from the post-init state with
the IR setter result. -/
private theorem nativeResultsMatchOn_storeHit_postInit
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore) (arg : Nat) :
    let yulTx := YulTransaction.ofIR tx
    let slots := Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode simpleStorageIRContract) observableSlots
    let initialWithStore : EvmYul.Yul.State :=
      .Ok (ssShared yulTx initialState.storage slots) store
    let withValue := initialWithStore.insert "value"
      (Backends.StateBridge.natToUInt256 arg)
    let haltState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Backends.StateBridge.natToUInt256 arg))
    nativeResultsMatchOn observableSlots
      { success := true
        returnValue := none
        finalStorage :=
          Compiler.Proofs.abstractStoreStorageOrMapping initialState.storage 0 (arg % evmModulus)
        finalMappings := Compiler.Proofs.storageAsMappings
          (Compiler.Proofs.abstractStoreStorageOrMapping initialState.storage 0 (arg % evmModulus))
        events := initialState.events }
      (.ok (Backends.Native.projectResult yulTx initialState.storage
        initialState.events (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨0⟩)))) := by
  intro yulTx slots initialWithStore withValue haltState
  simp only [Backends.Native.projectResult]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro slot hslot
    have hNative := projectStorageFromState_storeHit_postInit_materialized
      ssNC yulTx
      initialState.storage slots store arg slot (mem_materializedStorageSlots_of_mem _ _ _ hslot)
    have hArgMod : EvmYul.UInt256.ofNat arg = EvmYul.UInt256.ofNat (arg % evmModulus) := by
      unfold EvmYul.UInt256.ofNat
      simp [Id.run, Fin.ofNat, evmModulus, EvmYul.UInt256.size]
    simpa [haltState, withValue, initialWithStore,
      Compiler.Proofs.abstractStoreStorageOrMapping,
      Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, hArgMod] using hNative.symm
  · have hLogs : Backends.Native.projectLogsFromState haltState = [] := by
      simp only [Backends.Native.projectLogsFromState, haltState, withValue, initialWithStore,
        EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
        EvmYul.Yul.State.insert, EvmYul.State.sstore, EvmYul.State.setAccount,
        EvmYul.State.lookupAccount, EvmYul.State.addAccessedStorageKey,
        EvmYul.Account.updateStorage, EvmYul.Substate.addAccessedStorageKey, Option.option]
      split <;> rfl
    rw [hLogs, List.append_nil]

/-- Store-hit direct match when calldata carries the setter argument. -/
private theorem simpleStorageNativeStoreHitMatch_arg
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (arg : Nat) (rest : List Nat)
    (hStore : tx.functionSelector % Constants.selectorModulus = 0x6057361d)
    (hSelectorEq : tx.functionSelector = 0x6057361d)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) (hArgs : tx.args = arg :: rest) :
    nativeDispatcherExecMatchesIRPositive simpleStorageNativeDispatcherFuel
      simpleStorageIRContract tx initialState observableSlots
      ssNC := by
  obtain ⟨store, haltState, hExec, rfl⟩ :=
    simpleStorageNativeContract_dispatcherExec_storeHit_halt_atFuel
      (YulTransaction.ofIR tx) initialState.storage _ arg rest
      (by simpa [YulTransaction.ofIR] using hArgs)
      (by simpa using hStore.symm)
      (by simpa [YulTransaction.ofIR, evmModulus, Verity.Core.UINT256_MODULUS] using hNoWrap)
      (by simpa [YulTransaction.ofIR] using hMsgValue)
  refine nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match
    (by simpa [simpleStorage_runtimeCode_eq_single_dispatcher] using hExec) rfl ?_
  rw [interpretIR_simpleStorage_storeHit_arg tx initialState arg rest hSelectorEq hArgs
    (by simpa [evmModulus, EvmYul.UInt256.size] using hMsgValue)]
  exact nativeResultsMatchOn_storeHit_postInit tx initialState observableSlots store arg

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
    rwa [Nat.mod_eq_of_lt hselector] at hRetrieve
  have hMsgValue := simpleStorage_msgValue_mod_zero_of_dispatchGuardSafe tx hdispatchGuardSafe
  obtain ⟨store, hExec⟩ :=
    simpleStorageNativeContract_dispatcherExec_retrieveHit_halt_atFuel
      (YulTransaction.ofIR tx) initialState.storage
      (Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode simpleStorageIRContract) observableSlots)
      (by simpa using hRetrieve.symm)
      (by simpa [YulTransaction.ofIR, evmModulus, Verity.Core.UINT256_MODULUS] using hNoWrap)
      (by simpa [YulTransaction.ofIR] using hMsgValue)
  refine nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match
    (by simpa [simpleStorage_runtimeCode_eq_single_dispatcher] using hExec) rfl ?_
  rw [interpretIR_simpleStorage_retrieveHit tx initialState hSelectorEq
    (by simpa [evmModulus, EvmYul.UInt256.size] using hMsgValue)]
  exact nativeResultsMatchOn_mstore0_sload0_return32_postInit simpleStorageIRContract tx
    initialState observableSlots ssNC store

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
    rwa [Nat.mod_eq_of_lt hselector] at hStore
  have hMsgValue := simpleStorage_msgValue_mod_zero_of_dispatchGuardSafe tx hdispatchGuardSafe
  cases hArgs : tx.args with
  | nil =>
      exact simpleStorageNativeStoreHitMatch_short tx initialState observableSlots
        hStore hSelectorEq hNoWrap hMsgValue hArgs
  | cons arg rest =>
      exact simpleStorageNativeStoreHitMatch_arg tx initialState observableSlots arg rest
        hStore hSelectorEq hNoWrap hMsgValue hArgs

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
            % Constants.selectorModulus
            < Constants.selectorModulus :=
        Nat.mod_lt _ (by decide)
      exact Nat.lt_trans hMod (by decide)
    · change tx.functionSelector % selectorModulus ≠ _
      exact hSelMissStore
    · change tx.functionSelector % selectorModulus ≠ _
      exact hSelMissRetrieve
    · change 4 + tx.args.length * 32 < EvmYul.UInt256.size
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
      tx.functionSelector % Constants.selectorModulus = 0x2e64cec1
  · exact hRetrieveHit hR
  · by_cases hS :
        tx.functionSelector % Constants.selectorModulus = 0x6057361d
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
        ssNC) := by
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
    Backends.Native.callDispatcher_succ_eq_callDispatcherBlockResult,
    Backends.Native.callDispatcherBlockResult_initialState_eq_contractDispatcherBlockResult,
    Backends.Native.contractDispatcherBlockResult_eq_execResult
  ]
  convert hConcrete using 1 ;
    simp [simpleStorageNativeDispatcherFuel, simpleStorage_runtimeCode_eq_single_dispatcher,
      EvmYul.Yul.Ast.FunctionDefinition.rets] ; rfl

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
        ssNC) := by
  exact
    sourceResultMatchesNativeOn_of_sourceResultMatchesIRResult_of_nativeResultsMatchOn
      hSourceIR
      (simpleStorage_endToEnd_native_evmYulLean tx initialState observableSlots
        hselector hNoWrap hdispatchGuardSafe)

/-- Denote-headed SimpleStorage native theorem: the compiler-free denotation of
an event-free, byte-transport-free function matches the projected `EvmYul.Yul.callDispatcher` result
whenever the trusted source interpretation matches the IR result. -/
theorem simpleStorage_denote_endToEnd_native_evmYulLean_of_sourceIR
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (spec : CompilationModel.CompilationModel) (fn : CompilationModel.FunctionSpec)
    (initialWorld : Verity.ContractState) (hnoEvents : spec.events = [])
    (hbyteFree : DenoteAgreement.stmtListByteFree fn.body = true)
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
        ssNC) :=
  denoteResultMatchesNativeOn_of_sourceResultMatchesNativeOn hnoEvents hbyteFree
    (simpleStorage_source_endToEnd_native_evmYulLean_of_sourceIR tx initialState
      observableSlots _ hselector hNoWrap hdispatchGuardSafe hSourceIR)

end Compiler.Proofs.EndToEnd
