# Architectural & Roadmap Review — Claude Fable 5.1 (`anthropic/claude-fable-5-1`)

# Architectural & Roadmap Review: Verity 2.0 / EVMYulLean 2.0

**Reviewer stance.** I treat the fact base in §1 of the brief as ground truth about what exists. Everything I propose below that is *not* in that fact base is marked **(new)**; where I reference an existing module I use **(exists)**. Where I make an assumption about the internal shape of an existing definition that the brief does not pin down, I say so explicitly, because the wiring plan depends on those shapes and you should verify them before committing to the ordering.

The review is organized around a single invariant that I believe should govern every remaining milestone:

> **The active pipeline and the proved pipeline must be the same function.** Every theorem that is proved about a "hook" or "shim" that `Codegen.lean` does not actually call is, from a TCB perspective, worth zero. The last-mile work is not optional polish; it is the difference between "we proved a compiler" and "we proved a compiler that we don't ship."

---

## PART 1 — Completing the Verity Roadmap

### 1.0 TCB ledger (today vs. target)

Before ordering work, it helps to be precise about what is trusted *right now*, because each remaining phase is really a TCB-reduction step.

| Component | Status today | Trust reason | Target |
|---|---|---|---|
| Lean 4 kernel + `Mathlib` deps | trusted | unavoidable | trusted |
| `solidityMappingSlot_injective` | **1 axiom** | keccak collision-resistance | 0 axioms (convert to hypothesis, §1.2.3) |
| `solc --strict-assembly` (Yul → bytecode) | **trusted** | no verified assembler | out of TCB (§1.3.2) |
| `Import.lean` (15.7k LOC) | **trusted** | no witness automation | out of TCB per entrypoint via `SolcoreBridge` (§1.3.3) |
| `solc --standard-json` AST/`storageLayout` JSON reader | trusted | parser | trusted but shrunk to a ~1k-LOC `AstReader` (§1.3.3) |
| `Codegen.lean` default path (linear `buildSwitch`, 12-rule `foundation`) | proved for the default path | — | proved for the *optimized* path (§1.1) |
| `CertifiedPatchPack`, `SlotCoalescingShim`, `SelectorDispatchTree`, `TempReuse` | **proved but not on the active path** | — | on active path under `EndToEnd` (§1.1) |
| `attachNonReentrantGuard` (post-`compileFunctionSpec`) | **unproved transformation** | runs outside `SupportedSpec` | inside `SupportedSpec` (§1.2.4) |
| `helperSurfaceClosed` gate | **theorem exclusion** | catalog not threaded | retired (§1.2.1) |
| EVM reference (`EvmYul/EVM/*`, 255 theorems, 0 `sorryAx`) | spec (trusted as a model) | — | cross-validated against `revm`/`evmone`/EEST (§Part 2.2) |

The honest reading: the formal stack is already excellent *above* the Yul level, and the remaining risk is concentrated in (a) the gap between proved and active, and (b) the two external tools at the bottom and top of the pipeline.

---

### 1.1 Closing the "last mile": proved hooks → active pipeline

#### 1.1.1 The structural problem

The brief states that `Codegen.lean` defaults to linear `buildSwitch` and the 12-rule `foundation` expression pack, with `StmtRule`/`BlockRule`/`ObjectRule` foundation bundles empty, while `CertifiedPatchPack`, `SlotCoalescingShim`, and `SelectorDispatchTree` are proved standalone. This is the classic "optional pass" trap. The fix is to make the pipeline a *single parameterized function* whose parameter is itself a proof-carrying object, so that "optimized" and "legacy" are both instances of the same theorem.

**(new) `Compiler/Codegen/Profile.lean`**

```lean
/-- Everything that can vary between the legacy and optimized pipelines,
    bundled with the proofs that make it admissible. -/
structure CodegenProfile where
  fork          : EvmYul.Fork                       -- Shanghai | Cancun | Prague | Osaka
  exprPack      : CertifiedPatchPack ExprPatchRule
  stmtPack      : CertifiedPatchPack StmtPatchRule
  blockPack     : CertifiedPatchPack BlockPatchRule
  objectPack    : CertifiedPatchPack ObjectPatchRule
  dispatch      : DispatchStrategy                  -- .linearSwitch | .tree
  slotCoalesce  : Bool
  tempReuse     : TempReuseConfig
  shims         : ShimTable                         -- VerifiedCompilerShim recognizers
  -- Admissibility: each component carries its own soundness theorem.
  dispatch_sound  : DispatchStrategy.Sound dispatch
  coalesce_sound  : slotCoalesce = true → SlotCoalescingShim.Sound fork
  temp_sound      : TempReuse.Sound tempReuse

namespace CodegenProfile
def legacy    : CodegenProfile := { fork := .Cancun, exprPack := foundation12, stmtPack := .empty, ... dispatch := .linearSwitch, slotCoalesce := false, ... }
def optimized (f : Fork) : CodegenProfile := { fork := f, exprPack := certifiedExpr, stmtPack := certifiedStmt, ..., dispatch := .tree, slotCoalesce := true, ... }
end CodegenProfile
```

Then `Compiler/Codegen.lean` (exists) is refactored so that its entry point is

```lean
def emitYul (p : CodegenProfile) (ir : IRContract) : YulObject
```

and the *current* behavior is literally `emitYul CodegenProfile.legacy`. This is the key non-breaking move: every existing parity pack and every existing theorem about `Codegen` is restated as a theorem about `emitYul .legacy`, which is definitionally the old function if you do the refactor as pure parameter extraction (no semantic change). You can enforce "definitionally the same" in CI with a golden-output test: `emitYul .legacy ir` byte-equals the pre-refactor output for every contract in the parity corpus. Only after that test is green do you add `.optimized`.

#### 1.1.2 Wiring `CertifiedPatchPack`

Assumption about the existing shape (verify): `CertifiedPatchRule` bundles a rule with `preserves_eval : ∀ σ e, evalExpr σ (rule e) = evalExpr σ e` (or the `Option`/`Except` equivalent for rules that fire conditionally), and `CertifiedPatchPack` is a list with a fold `applyPack`.

The theorem that needs to exist, if it does not already, is the **lifting** from expression-level preservation to object-level preservation under the EvmYul Yul semantics, *not* under Verity's own Yul evaluator:

```lean
-- (new) Compiler/Yul/PatchFrameworkLifting.lean
theorem applyExprPack_preserves_object
    (pack : CertifiedPatchPack ExprPatchRule) (obj : YulObject) :
    ∀ (fuel : Nat) (σ : EvmYul.Yul.State),
      EvmYul.Yul.execObject fuel (applyExprPack pack obj) σ
        = EvmYul.Yul.execObject fuel obj σ
```

Two subtleties that a reviewer should insist on:

1. **Evaluation order.** Yul evaluates function-call arguments right-to-left and expressions can have side effects (`sload`, `call`, `mload` after `mstore`). An `ExprPatchRule` that rewrites `add(x, 0) → x` is fine, but any rule that reorders or duplicates subexpressions (e.g. CSE of `sload(s)`) is *not* an expression-local rewrite. The `CertifiedPatchRule.preserves_eval` contract must be stated relative to EvmYul's `evalExpr` with its `State` threading, so that a rule which duplicates an effectful subterm cannot be certified. If the current framework proves preservation against a pure `Expr → Word` evaluator, the lifting theorem above will not go through — and that is the correct outcome; it tells you the pack needs re-certification against `EvmYul.Yul`.
2. **Gas dominance is not implied by `preserves_eval`.** A rule can be semantics-preserving and *increase* gas (e.g. rewriting `shl(1,x)` to `mul(x,2)` on a fork where `SHL` is cheaper). `CertifiedPatchRule` should therefore carry a second obligation `improves_cost : ∀ σ, yulGas fork σ (rule e) ≤ yulGas fork σ e` using `EvmYul/Yul/GasInterpreter.lean` (exists). See §1.1.5 for why this must be fork-indexed.

Populate the empty bundles in dependency order:
- **Stmt pack** (first, cheapest proofs): `let x := y` forwarding, dead `let` elimination (requires an effect-freedom predicate `Expr.Pure` — define it via `StmtFeatureMask` reuse), `if 1 { b } → b`, `if 0 { b } → ∅`, `switch` with single case → `if`.
- **Block pack**: `SlotCoalescingShim` (exists) becomes a `BlockPatchRule` (§1.1.3); `TempReuse` becomes a `BlockPatchRule` over function bodies.
- **Object pack**: `SelectorDispatchTree` (§1.1.4) and `yulOutlinedHelper` (exists, as a `VerifiedECMShims` family) — outlining of repeated statement sequences into Yul functions.

#### 1.1.3 Wiring `SlotCoalescingShim`

The brief describes intra-block `SLOAD` CSE and packed subfield `SLOAD`/`SSTORE` fusion. The right place in the pipeline is **after** `TempReuse` allocation is decided but **before** patch-pack expression rewriting, because coalescing introduces `let` temporaries that the expression pack should then simplify.

Soundness is *not* intra-block in the naive sense: between two `sload(s)` there may be `call`/`delegatecall`/`staticcall` (reentrancy can write `s`), `sstore(s', _)` with `s'` possibly aliasing `s` (needs `StateLensAlgebra` disjointness or syntactic slot equality), or `create`/`create2`. The soundness theorem should be shaped as

```lean
-- in Compiler/Proofs/SlotCoalescingShim.lean (exists; extend)
theorem coalesce_block_sound (fork : Fork) (b : YulBlock)
    (h : NoInterveningClobber b) :
    ∀ σ, execBlock fork (coalesceSloads b) σ = execBlock fork b σ
```

where `NoInterveningClobber` is decidable and computed by the same `StmtFeatureMask` catamorphism in `UsageAnalysis.lean` (exists) extended to Yul (a `YulFeatureMask`: `hasCall`, `hasSstoreTo : Set Expr`, `hasCreate`). The shim runs only when the decision procedure returns `true`, so the active path is always inside the theorem's hypothesis.

For **cross-branch** coalescing (reads hoisted above an `if`, writes sunk below it — a major source of the gas gap noted in Part 2), do *not* attempt dominance-frontier SSA in Yul. Instead do it one level up, at `TypedIR` (Layer 2), where `IRContract` has structured control flow: a `IRPass.hoistInvariantSload` with a Layer 2 preservation theorem against `Denote.execStmt`. The IR level has an algebraic storage frame (`unchangedExcept`, 5-channel `StorageLoc`) which is exactly the vocabulary needed to prove "the slot read in both branches is the same lens and nothing between the branch point and the reads writes through that lens."

Gas dominance for coalescing is trivially true under EIP-2929 (a second `SLOAD` of a warm slot costs 100 but a `let` costs ~3–6), but you must still state it in the fork-indexed model (§1.1.5).

#### 1.1.4 Wiring `SelectorDispatchTree`

The theorem that matters is **extensional dispatch equality**, not Yul equality:

```lean
-- Compiler/Selector.lean (exists; add)
theorem dispatchTree_selects_same (fns : List (Selector × FnLabel)) (hnodup : fns.map Prod.fst |>.Nodup) :
    ∀ sel, lookupTree (buildTree fns)
