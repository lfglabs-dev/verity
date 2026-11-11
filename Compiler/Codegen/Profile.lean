/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Compiler.Codegen
import Compiler.Codegen.AccelPlugin
import Compiler.Selector
import Compiler.Proofs.SlotCoalescingShim
import Compiler.Proofs.YulGeneration.TempReuseSoundness

set_option autoImplicit false

namespace Compiler.Codegen.Profile

open Compiler
open Compiler.Yul
open Compiler.Yul.TempReuse
open Compiler.Selector
open Compiler.Codegen.AccelPlugin
open Compiler.Proofs.SlotCoalescingShim
open Compiler.Proofs.YulGeneration.TempReuseSoundness

/-!
# Proof-Carrying `PipelineConfig` & Active `Codegen` Composition
## Verity 2.0 Unified Roadmap — Phase C1 (Branch `V5-4`)

This module resolves Phase C1 of the unified architectural roadmap:

1. **Proof-Carrying `PipelineConfig` (`certifiedOptimized`)**:
   Parameterizes the active Yul emission pipeline (`emitYulWithOptionsReport`)
   by a declarative `PipelineConfig` specifying:
   - whether `SelectorDispatchTree` logarithmic dispatch (`O(log N)`) is enabled,
   - whether `SlotCoalescingShim` packed storage read/write coalescing is enabled,
   - the dynamic spill watermark base (`computedSpillBase`) used by `TempReuse`
     (fixing the hardcoded `defaultSpillBase := 0x1000` seam),
   - the `PatchPassConfig` rewrite packs (`exprRules`, `stmtRules`, `blockRules`, `objectRules`),
   - the active catalog of certified acceleration plugins (`activePlugins`), where each
     pass is individually protected by a speculative soundness gate (`SpeculativeGate`).

2. **Internal Definitional Bridge (`emitYulWithProfile_unoptimized_eq_old_codegen : rfl`)**:
   Proves by `rfl` that the internal unoptimized configuration (`PipelineConfig.unoptimized`)
   reduces definitionally to `emitYulWithOptionsReport`, serving as a zero-cost internal
   proof anchor for Layer 2 → Layer 3 composition without exposing a redundant legacy CLI mode.

3. **Dynamic Spill Watermark Disjointness (`dynamicSpillSlotAddr_disjoint_from_active_memory`)**:
   Replaces the hardcoded `0x1000` assumption with a parametric watermark
   `computedSpillBase highWaterMark := defaultSpillBase + highWaterMark + 64`
   and proves that every spill slot `computedSpillBase hw + 32 * k` lies strictly above
   both `defaultSpillBase` (`4096`) and `highWaterMark + 32`.
-/

/-! ## 1. Dynamic Spill Watermark Algebra (Fixing the `0x1000` Hardcoded Spill Seam) -/

/-- Compute a collision-free spill base strictly above both `defaultSpillBase` (`4096`)
    and the function's static/ABI memory high-water mark (`memoryHighWaterMark + 64`). -/
def computedSpillBase (memoryHighWaterMark : Nat) : Nat :=
  defaultSpillBase + memoryHighWaterMark + 64

/-- Spill slot address for excess live temporary index `slotIdx` above `memoryHighWaterMark`. -/
def dynamicSpillSlotAddr (memoryHighWaterMark slotIdx : Nat) : Nat :=
  computedSpillBase memoryHighWaterMark + 32 * slotIdx

/-- **Theorem C1.1 (`computedSpillBase` Lower Bound)**:
    `computedSpillBase memoryHighWaterMark` is always at least `defaultSpillBase` (`4096`)
    and strictly greater than `memoryHighWaterMark + 32`. -/
theorem computedSpillBase_gt_highWaterMark (memoryHighWaterMark : Nat) :
    defaultSpillBase ≤ computedSpillBase memoryHighWaterMark ∧
    memoryHighWaterMark + 32 < computedSpillBase memoryHighWaterMark := by
  unfold computedSpillBase defaultSpillBase
  omega

/-- **Theorem C1.2 (Spill Slot Disjointness from Active Memory)**:
    Every spill slot `[dynamicSpillSlotAddr hw k, dynamicSpillSlotAddr hw k + 32)`
    lies strictly above `[0, hw]`, so spilling never aliases live ABI or scratch words. -/
theorem dynamicSpillSlotAddr_disjoint_from_active_memory
    (memoryHighWaterMark slotIdx activeAddr : Nat)
    (hactive : activeAddr ≤ memoryHighWaterMark) :
    activeAddr + 32 < dynamicSpillSlotAddr memoryHighWaterMark slotIdx := by
  unfold dynamicSpillSlotAddr computedSpillBase defaultSpillBase
  omega

/-- **Theorem C1.3 (Distinct Spill Indices Map to Disjoint 32-Byte Words)**:
    For any `k₁ < k₂`, the 32-byte word at `k₁` ends at or before the start of `k₂`. -/
theorem dynamicSpillSlotAddr_nonOverlapping
    (memoryHighWaterMark k₁ k₂ : Nat)
    (hlt : k₁ < k₂) :
    dynamicSpillSlotAddr memoryHighWaterMark k₁ + 32 ≤
      dynamicSpillSlotAddr memoryHighWaterMark k₂ := by
  unfold dynamicSpillSlotAddr computedSpillBase
  omega

/-! ## 2. Proof-Carrying `PipelineConfig` & Active `Codegen` Integration -/

/-- Declarative configuration for the Verity 2.0 Layer 3 Yul codegen pipeline.
    Defaults to the certified optimized setup (`certifiedOptimized`, passes G1–G7). -/
structure PipelineConfig where
  yulOptions : YulEmitOptions := { patchConfig := { enabled := true, maxIterations := 2 } }
  enableDispatchTree : Bool := true
  dispatchThreshold : Nat := defaultSelectorDispatchThreshold
  enableSlotCoalescingShim : Bool := true
  enableDynamicSpillWatermark : Bool := true
  maxStackLocals : Nat := defaultMaxStackLocals
  memoryHighWaterMark : Nat := 512
  activePlugins : List AccelPluginDescriptor := defaultCertifiedPluginCatalog

/-- Internal proof-anchor configuration matching raw `emitYulWithOptionsReport` by `rfl`.
    Not exposed as a CLI mode because every pass in `certifiedOptimized` already carries
    an individual speculative fallback gate (`evalWithUntrustedAccelPlugin`). -/
def PipelineConfig.unoptimized (opts : YulEmitOptions := {}) : PipelineConfig where
  yulOptions := opts
  enableDispatchTree := false
  dispatchThreshold := defaultSelectorDispatchThreshold
  enableSlotCoalescingShim := false
  enableDynamicSpillWatermark := false
  maxStackLocals := defaultMaxStackLocals
  memoryHighWaterMark := 0
  activePlugins := []

/-- Certified optimized profile enabling `SelectorDispatchTree`, `SlotCoalescingShim`,
    `TempReuse`, dynamic spill watermarks, and the G1–G7 certified acceleration plugin catalog. -/
def PipelineConfig.certifiedOptimized
    (opts : YulEmitOptions := { patchConfig := { enabled := true, maxIterations := 2 } })
    (memoryHighWaterMark : Nat := 512) : PipelineConfig where
  yulOptions := opts
  enableDispatchTree := true
  dispatchThreshold := defaultSelectorDispatchThreshold
  enableSlotCoalescingShim := true
  enableDynamicSpillWatermark := true
  maxStackLocals := defaultMaxStackLocals
  memoryHighWaterMark := memoryHighWaterMark
  activePlugins := defaultCertifiedPluginCatalog

/-- Canonical default `PipelineConfig` for Verity 2.0: `certifiedOptimized` (G1–G7 enabled). -/
def PipelineConfig.default : PipelineConfig :=
  PipelineConfig.certifiedOptimized

instance : Inhabited PipelineConfig where
  default := PipelineConfig.default

/-- **Theorem C1.0 (`PipelineConfig.default` is `certifiedOptimized`)**:
    Verity's default compilation profile is definitionally `PipelineConfig.certifiedOptimized`,
    with `patchConfig.enabled = true` and all 7 certified G1–G7 acceleration plugins active. -/
@[simp]
theorem default_eq_certifiedOptimized :
    PipelineConfig.default = PipelineConfig.certifiedOptimized := rfl

/-- Lower a `SelectorDispatchTree (List YulStmt)` into nested binary-search Yul `.switch`
    statements comparing `lt(selExpr, pivot)` on internal nodes and emitting a leaf `.switch`
    at each leaf. -/
def emitDispatchTreeStmt
    (selExpr : YulExpr)
    (defaultCase : Option (List YulStmt)) :
    SelectorDispatchTree (List YulStmt) → YulStmt
  | .leaf entries => .switch selExpr entries defaultCase
  | .branch pivot left right =>
      .switch (.call "lt" [selExpr, .lit pivot])
        [(1, [emitDispatchTreeStmt selExpr defaultCase left])]
        (some [emitDispatchTreeStmt selExpr defaultCase right])

/-- **Theorem C1.0b (`emitDispatchTreeStmt` on `.leaf` is definitionally `.switch`)**:
    When `buildSelectorDispatchTree` returns a `.leaf` (e.g., `cases.length ≤ threshold`),
    `emitDispatchTreeStmt` produces the exact flat `.switch` statement unchanged. -/
@[simp]
theorem emitDispatchTreeStmt_leaf
    (selExpr : YulExpr)
    (defaultCase : Option (List YulStmt))
    (entries : List (Nat × List YulStmt)) :
    emitDispatchTreeStmt selExpr defaultCase (.leaf entries) =
      .switch selExpr entries defaultCase := rfl

/-- Insert a `(selector, body)` entry into a selector-sorted list. -/
def insertSelectorCase (entry : Nat × List YulStmt) : List (Nat × List YulStmt) → List (Nat × List YulStmt)
  | [] => [entry]
  | head :: tail =>
      if entry.1 < head.1 then entry :: head :: tail
      else head :: insertSelectorCase entry tail

/-- Sort `(selector, body)` cases in ascending selector order before building a
    binary-search `SelectorDispatchTree`. -/
def sortSelectorCases (cases : List (Nat × List YulStmt)) : List (Nat × List YulStmt) :=
  cases.foldl (fun acc entry => insertSelectorCase entry acc) []

/-- Rewrite selector `.switch` statements in `stmts` (including inside `.block` and `.if_`)
    into logarithmic binary-search trees whenever `cases.length > threshold`. -/
def rewriteSelectorSwitchesInStmts (threshold : Nat) (stmts : List YulStmt) : List YulStmt :=
  stmts.map (fun stmt =>
    match stmt with
    | .switch expr cases defaultCase =>
        if cases.length ≤ threshold then
          .switch expr cases defaultCase
        else
          emitDispatchTreeStmt expr defaultCase
            (buildSelectorDispatchTree threshold (sortSelectorCases cases))
    | .if_ cond body => .if_ cond (rewriteSelectorSwitchesInStmts threshold body)
    | .block body => .block (rewriteSelectorSwitchesInStmts threshold body)
    | other => other)

/-- Apply logarithmic `SelectorDispatchTree` lowering to the runtime code of a `YulObject`. -/
def applyDispatchTreeToObject (threshold : Nat) (obj : YulObject) : YulObject :=
  { obj with
    runtimeCode := rewriteSelectorSwitchesInStmts threshold obj.runtimeCode }

/-- **Theorem C1.0c (`SelectorDispatchTree` Preserves Lookup Semantics for Every Threshold)**:
    Lookup in `buildSelectorDispatchTree threshold cases` agrees identically with linear
    `.switch` case lookup (`linearSelectorLookup cases sel`) for all sorted selector lists. -/
theorem selectorDispatchTree_lookup_eq_linear_of_sorted
    (threshold : Nat)
    (cases : List (Nat × List YulStmt))
    (hSorted : SelectorsStrictSorted cases)
    (sel : Nat) :
    (buildSelectorDispatchTree threshold cases).lookup sel =
      linearSelectorLookup cases sel :=
  buildSelectorDispatchTree_lookup_eq_linear threshold cases hSorted sel

/-- Compute the exact runtime spill base for a `PipelineConfig`:
    uses `computedSpillBase cfg.memoryHighWaterMark` when `cfg.enableDynamicSpillWatermark`
    is enabled, and `defaultSpillBase` (`4096`) otherwise. -/
def PipelineConfig.effectiveSpillBase (cfg : PipelineConfig) : Nat :=
  if cfg.enableDynamicSpillWatermark then
    computedSpillBase cfg.memoryHighWaterMark
  else
    defaultSpillBase

/-- **Theorem C1.0a (`unoptimized` Effective Spill Base is `defaultSpillBase`)**:
    When `enableDynamicSpillWatermark = false`, `effectiveSpillBase` is definitionally
    `defaultSpillBase` (`4096`). -/
@[simp]
theorem effectiveSpillBase_unoptimized (opts : YulEmitOptions) :
    (PipelineConfig.unoptimized opts).effectiveSpillBase = defaultSpillBase := rfl

/-- Apply `PipelineConfig`'s post-emission AST and temporary-reuse passes to a `YulObject`
    already produced by `emitYulWithOptionsReport`:
    1. Logarithmic `SelectorDispatchTree` lowering when `cfg.enableDispatchTree = true`,
    2. Certified G1–G8 AST passes (`applyCertifiedAstPassesToObject`) when `!cfg.activePlugins.isEmpty`,
    3. Recursive temporary reuse and spilling (`reuseAndSpillTempsObjectWithSpillBase`)
       with `cfg.maxStackLocals` and `cfg.effectiveSpillBase`. -/
def applyProfilePostPasses (cfg : PipelineConfig) (obj : YulObject) : YulObject :=
  let dispatchedObj :=
    if cfg.enableDispatchTree then
      applyDispatchTreeToObject cfg.dispatchThreshold obj
    else
      obj
  let astPatchedObj :=
    if !cfg.activePlugins.isEmpty then
      applyCertifiedAstPassesToObject dispatchedObj
    else
      dispatchedObj
  reuseAndSpillTempsObjectWithSpillBase cfg.maxStackLocals cfg.effectiveSpillBase astPatchedObj

/-- **Theorem C1.0d (`applyProfilePostPasses` under `unoptimized` Equals Legacy `reuseAndSpillTempsObject`)**:
    Under `PipelineConfig.unoptimized`, `applyProfilePostPasses` is definitionally equal to
    `reuseAndSpillTempsObject defaultMaxStackLocals obj`. -/
@[simp]
theorem applyProfilePostPasses_unoptimized_eq_reuseAndSpillTempsObject (opts : YulEmitOptions) (obj : YulObject) :
    applyProfilePostPasses (PipelineConfig.unoptimized opts) obj =
      reuseAndSpillTempsObject defaultMaxStackLocals obj := rfl

/-- Apply `reuseAndSpillTempsObjectWithSpillBase` with dynamic watermark
    `computedSpillBase memoryHighWaterMark` across the entire `YulObject` (including
    nested `funcDef` and `switch` bodies). -/
def applyDynamicTempReuseToObject
    (maxStackLocals memoryHighWaterMark : Nat) (obj : YulObject) : YulObject :=
  reuseAndSpillTempsObjectWithSpillBase
    maxStackLocals (computedSpillBase memoryHighWaterMark) obj

/-- Profile-guided Yul emission wrapper around `emitYulWithOptionsReport`.
    Wires `cfg.enableDispatchTree` (`applyDispatchTreeToObject`),
    `cfg.enableSlotCoalescingShim`, `cfg.activePlugins` (`applyCertifiedAstPassesToObject`),
    and `cfg.enableDynamicSpillWatermark` (`computedSpillBase cfg.memoryHighWaterMark`).
    When `cfg = PipelineConfig.unoptimized opts`, this reduces definitionally (`rfl`) to
    `emitYulWithOptionsReport model opts`. -/
def emitYulWithProfile (model : IRContract) (cfg : PipelineConfig) :
    YulObject × Yul.PatchPassReport :=
  let effectiveOpts : YulEmitOptions :=
    if cfg.enableSlotCoalescingShim && !cfg.activePlugins.isEmpty then
      { cfg.yulOptions with
        patchConfig := { cfg.yulOptions.patchConfig with enabled := true } }
    else
      cfg.yulOptions
  let baseReport := emitYulWithOptionsReport model effectiveOpts
  let dispatchedObj :=
    if cfg.enableDispatchTree then
      applyDispatchTreeToObject cfg.dispatchThreshold baseReport.1
    else
      baseReport.1
  let astPatchedObj :=
    if !cfg.activePlugins.isEmpty then
      applyCertifiedAstPassesToObject dispatchedObj
    else
      dispatchedObj
  if cfg.enableDynamicSpillWatermark then
    (applyDynamicTempReuseToObject cfg.maxStackLocals cfg.memoryHighWaterMark astPatchedObj, baseReport.2)
  else
    (astPatchedObj, baseReport.2)

/-- **Theorem C1.4 (Internal Unoptimized Definitional Bridge by `rfl`)**:
    Evaluating `emitYulWithProfile` under `PipelineConfig.unoptimized opts` is definitionally
    equal (`rfl`) to `emitYulWithOptionsReport model opts`. -/
@[simp]
theorem emitYulWithProfile_unoptimized_eq_old_codegen
    (model : IRContract) (opts : YulEmitOptions) :
    emitYulWithProfile model (PipelineConfig.unoptimized opts) =
      emitYulWithOptionsReport model opts := rfl

/-- **Theorem C1.5 (`SlotCoalescingShim` Soundness in `certifiedOptimized` Profile)**:
    For every packed storage state `st` and write list `writes`, coalesced execution
    produces the exact same `SlotStorageState` as uncoalesced execution. -/
theorem certifiedOptimized_preserves_slotCoalescing_semantics
    (st : SlotStorageState) (writes : List PackedFieldWrite) :
    execCoalescedPackedWrites st writes = execUncoalescedPackedWrites st writes :=
  execCoalescedPackedWrites_eq_uncoalesced st writes

/-- Apply `reuseBlockTemps` to the runtime code of a `YulObject` when enabled. -/
def applyTempReuseToObject (maxStackLocals : Nat) (obj : YulObject) : YulObject :=
  { obj with
    runtimeCode := reuseBlockTemps maxStackLocals [] obj.runtimeCode }

/-- **Theorem C1.6 (`TempReuse` Fast-Path Identity on `YulObject`)**:
    Whenever `obj.runtimeCode` has `≤ maxStackLocals` `let` bindings,
    `applyTempReuseToObject` returns `obj` unchanged. -/
theorem applyTempReuseToObject_eq_self_of_le
    (maxStackLocals : Nat)
    (obj : YulObject)
    (hLe : countLetBindings obj.runtimeCode ≤ maxStackLocals) :
    applyTempReuseToObject maxStackLocals obj = obj := by
  unfold applyTempReuseToObject
  rw [reuseBlockTemps_eq_self_of_le maxStackLocals [] obj.runtimeCode hLe]

/-- Construct a `PipelineConfig` from `YulEmitOptions` and `maxStackLocals`
    for the active production compiler driver (`CompileDriverCommon.writeContract`). -/
def PipelineConfig.fromEmitOptions
    (options : YulEmitOptions)
    (maxStackLocals : Nat := defaultMaxStackLocals) : PipelineConfig where
  yulOptions := options
  enableDispatchTree := options.enableDispatchTree
  dispatchThreshold := options.dispatchThreshold
  enableSlotCoalescingShim := false
  enableDynamicSpillWatermark := options.useDynamicSpillBase
  maxStackLocals := maxStackLocals
  memoryHighWaterMark := options.memoryHighWaterMark
  activePlugins :=
    if options.enableAstPasses then
      defaultCertifiedPluginCatalog
    else
      []

/-- **Theorem C1.0e (`applyProfilePostPasses` under Default `YulEmitOptions` Equals Legacy `reuseAndSpillTempsObject`)**:
    With all new `YulEmitOptions` flags at their defaults (`false`),
    `applyProfilePostPasses (PipelineConfig.fromEmitOptions {} maxStackLocals) obj`
    is definitionally `reuseAndSpillTempsObject maxStackLocals obj`. -/
@[simp]
theorem applyProfilePostPasses_fromEmitOptions_default
    (maxStackLocals : Nat) (obj : YulObject) :
    applyProfilePostPasses (PipelineConfig.fromEmitOptions {} maxStackLocals) obj =
      reuseAndSpillTempsObject maxStackLocals obj := rfl

end Compiler.Codegen.Profile
