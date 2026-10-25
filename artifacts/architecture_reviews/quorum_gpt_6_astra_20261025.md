# GPT-6 Astra Quorum Architectural Review: Verity 2.0 & EVMYulLean 2.0 (`2026-10-25`)

- **Cloud Mission ID**: `b076c416-9799-48e6-baa6-0b36341d6df0`
- **Action Receipt ID**: `69793899-7084-4917-a326-8604f1cba693`
- **Provider / Account / Model**: `hermes` / `paloma` / `openai/gpt-6-astra`
- **Idempotency Key**: `astra-6-quorum-spec-cleanup-20261025-v1`
- **Worktrees Audited**:
  - `EVMYulLean 2.0`: `/var/lib/sandboxed-node/worktrees/evmyullean`
  - `Verity 2.0`: `/var/lib/sandboxed-node/worktrees/wt-p3-uniswap-v4`

---

## Part I — Direct Ground-Truth Code & `turbo-lean --json audit-spec` Findings

### 1. `turbo-lean --json audit-spec` Quantitative Results (13 Target Modules, 289 Theorems)

| Worktree | Module | Total Specs | Tight | Vacuous | Trivial | Droppable Hyps | Ground-Truth Semantic Status |
|---|---|---:|---:|---:|---:|---:|---|
| `evmyullean` | `MetaSpecs/DialectCommutation.lean` | 12 | 12 | 0 | 0 | 0 | **Genuine semantic bridge**: links `effect` to actual `EvmYul.step (.Yul)` (`yul_step_effect`) and `EvmYul.step (.EVM)` (`evm_step_effect`) + `yulPrimOpDynamicGas` for 14 shared instructions. |
| `evmyullean` | `MetaSpecs/StateLensAlgebra.lean` | 65 | 65 | 0 | 0 | 0 | **Genuine local semantic theorem + duplicate instance hazard**: `sstore_eq_storageLens` connects to real `State.sstore`, but lines 165–193 re-declare duplicate `LawfulBEq UInt256`, `Std.TransCmp`, `Std.LawfulEqCmp`, and `Std.LawfulBEqCmp` instances already defined in `EvmYul/UInt256.lean:78-128`. |
| `evmyullean` | `MetaSpecs/GasTermination.lean` | 11 | 11 | 0 | 0 | 0 | **Disconnected termination model**: proves `evmTerminationMeasure` decreases under standalone `consumeYulGas` and `L(g)`, but neither `EVM/Semantics.lean` nor `Yul/Interpreter.lean` uses `evmTerminationMeasure` or `consumeYulGas`. |
| `evmyullean` | `MetaSpecs/StaticCallAndRollback.lean` | 8 | 8 | 0 | 0 | 0 | **Disconnected local-record model**: defines standalone `guardedTransition`, `CallFrameCheckpoint`, and `resolveFrameTermination` and proves `transactionalRollback_universal` by `rfl` on the local record update rather than on `EVM.step` or `Yul.primCall`. |
| `evmyullean` | `Specs/GasSpec.lean` | 12 | 12 | 0 | 0 | 0 | **Genuine pure gas-schedule lemmas**: proves properties of `EvmYul.EVM.L`, `Cₘ`, `CsloadPure`, `CsstorePure`, `Ckeccak256Pure`, `ClogPure`, `intrinsicGas`. |
| `evmyullean` | `Specs/YulEvmGasEquivalence.lean` | 24 | 22 | 0 | **2** | 0 | **2 trivial specs flagged by `turbo-lean`**: `yulStepTotalGas_nonneg` and `yulMemoryExpansionGas_nonneg` (`0 ≤ n` on `ℕ`, proved by `Nat.zero_le`). Remaining 22 theorems prove pure alignment between `yulPrimOpDynamicGas` and `EVM.Gas`, but `yulPrimOpDynamicGas` is not called by `Yul/Interpreter.lean`. |
| `evmyullean` | `Specs/MessageCallSimulation.lean` | 7 | 7 | 0 | 0 | 0 | **Disconnected helper simulation**: proves arithmetic properties of standalone `forwardedCallGas` and `prepareChildCallEnv`, not wired into `Yul/Interpreter.lean:primCall`. |
| `evmyullean` | `Specs/ConformMultiFork.lean` | 10 | 10 | 0 | 0 | 0 | **Pure fork-config & EIP-3529 arithmetic**: proves `ofNetworkString`, `effectiveGasRefund_le_fifth`, `prague_intrinsicGas_ge_cancun`. |
| `evmyullean` | `Specs/PureKeccak256.lean` | 6 | 6 | 0 | 0 | 0 | **Incomplete specification shell**: defines `roundConstants` (24 `UInt64`s) and `rotl64`, but **no Keccak-f[1600] permutation or sponge**. `evalKeccak256SliceWith_backend_equiv` takes `(hAgree : ∀ msg, pureHash msg = ffi.KEC msg)` as an unproved hypothesis. |
| `evmyullean` | `Specs/UInt256BitVecBridge.lean` | 17 | 17 | 0 | 0 | 0 | **Genuine foundational `UInt256` ↔ `BitVec 256` bridge**: proves ring/group identities via `bv_decide`, but lives only in `evmyullean` while Verity defines a second `Verity.Core.Uint256`. |
| `evmyullean` | `Specs/YellowPaperTraceability.lean` | 11 | 11 | 0 | 0 | 0 | **Pure gas equation lemmas + string metadata table**: duplicates `Cₘ ⟨0⟩ = 0`, `L n ≤ n`, and `intrinsicGas` monotonicity already in `GasSpec.lean` / `ConformMultiFork.lean`. |
| `wt-p3-uniswap-v4` | `Compiler/Codegen/AccelPlugin.lean` | 10 | 10 | 0 | 0 | 0 | **Meta-framework + string-allowlist registry**: `evalWithUntrustedAccelPlugin` and `VerifiedAccelContract` are clean higher-order combinators, but `verifiedAccelTheoremAllowlist : List String` and `defaultCertifiedPluginCatalog` (`G1..G55`) are unverified string descriptors not executed by `emitYulWithProfile`. |
| `wt-p3-uniswap-v4` | `Compiler/Autoresearch/MaxwellGasSuperoptimizer.lean` | 87 | 87 | 0 | 0 | 0 | **Disconnected `Nat`/tautology bloat (1412 lines)**: `validateSynthesizedSolcoreWitness` only checks `decide (s = d)` on two caller-supplied structs; `G8..G55` and 32 `burn` theorems prove generic `Nat` identities (`(x / d₁) / d₂ = x / (d₁ * d₂)`), `if ts = ts then v₂ else v₁ = v₂`, and `1 ≠ 2`, with zero connection to `IRContract`, `YulStmt`, or `emitYul`. |

### 2. Four Real Interpreter Bugs Exposed by Inspecting `EvmYul/Yul/Interpreter.lean`

Because `EvmYul/Yul/MessageCallCombinator.lean` (`prepareChildCallEnv`) and `EvmYul/MetaSpecs/StaticCallAndRollback.lean` (`guardedTransition`, `resolveFrameTermination`) were written as standalone sidecar modules and **never wired into `EvmYul/Yul/Interpreter.lean` (`primCall`)**, `Yul/Interpreter.lean` still contains 350 lines of copy-pasted message-call handling with four concrete semantic bugs:

1. **Bug 1 — Nested `STATICCALL` inside a `STATICCALL` throws `.StaticModeViolation` (`Yul/Interpreter.lean:172`)**:
   - Line 172 reads:
     ```lean
     | .STATICCALL =>
       match args with
         | _ :: address_arg :: inOffset :: inSize :: outOffset :: outSize :: _ =>
           if ¬s₀.executionEnv.perm then throw .StaticModeViolation
     ```
   - In the EVM (EIP-214), calling `STATICCALL` while already in static mode (`perm = false`) is completely legal (`effectivePerm .StaticCall false = false`). Throwing `.StaticModeViolation` breaks every view/pure function that makes a nested `staticcall` (e.g., router → pool `staticcall` → token `staticcall`).
2. **Bug 2 — Parent `calldata` is wiped to `ByteArray.empty` after any child call returns (`Yul/Interpreter.lean:120, 155, 212, 235, 296, 319`)**:
   - When restoring `executionEnv₃` after `callDispatcher`, `primCall` sets `calldata := default` instead of `calldata := s₀.executionEnv.calldata`. Any Yul function that reads `calldataload` or `calldatasize` after making an external call observes empty calldata!
3. **Bug 3 — Parent `depth` and `sender` are not properly restored/propagated (`Yul/Interpreter.lean:95-125`)**:
   - `executionEnv₁` sets `source := s₀.executionEnv.codeOwner` without updating `sender`, and `executionEnv₃` copies `sharedState₂.executionEnv` (which has `depth = s₀.executionEnv.depth + 1`) without restoring `depth := s₀.executionEnv.depth`.
4. **Bug 4 — Child `.Revert` and gas operand (`args[0]`) are ignored (`Yul/Interpreter.lean:74, 133`)**:
   - `primCall` ignores the gas limit argument (`_ :: address_arg :: ...`), never invokes `consumeYulGas` or `yulPrimOpDynamicGas` from `Yul/GasInterpreter.lean`, and propagates `.error .Revert` directly to the top level (`| .error e => .error e`) instead of catching child revert, rolling back world state to `s₀`, and returning `0` on the Yul stack.

---

## Part II — Full Verbatim Report from Cloud Mission (`openai/gpt-6-astra`)

# Architectural review

Scope: read-only. The two requested worktrees are not mounted in this runtime, so this review is grounded in the architecture summary you provided. I am not treating module names or theorem names as evidence beyond the stated theorem bodies and wiring facts.

The central finding is structural:

EVMYulLean contains several useful local semantic lemmas, but its major “end-to-end” claims currently terminate at disconnected transition records, gas functions, or effect models. Verity’s optimization and acceleration layers are even further from the compiler pipeline: most certificates are names, strings, digest equality, or arithmetic identities over the wrong domain. The system is not yet a verified optimizing compiler. It is a compiler with a partially verified semantic substrate and several unconnected proof-shaped components.

## (A) Critical audit

### A.1 Classification rule

A theorem is a genuine semantic theorem only if its conclusion is connected to at least one of:

1. the actual `EVM.step` or `Yul.step`;
2. actual `State.sstore` or another executable state transition;
3. the actual `emitYul`/IR/code-generation path;
4. a checked refinement relation that composes those layers.

A theorem over an isolated record, a standalone pure function, a `Nat` identity, a string registry, or equality of preconstructed summaries is not an implementation theorem.

### A.2 EVMYulLean modules

| Module | Classification | Assessment |
|---|---|---|
| `EvmYul/UInt256.lean` | Genuine foundational semantic substrate, not by itself an EVM theorem | The `BitVec 256` representation, `Fin` projection, comparison instances, and signed/unsigned operators are valuable. They become semantic evidence only when the interpreter and opcode semantics consume this exact type. The main architectural risk is duplicate instances elsewhere. |
| `EvmYul/EVM/Gas.lean` | Pure executable specification; local semantic content | The fork table and pure gas functions are useful and can be authoritative if `EVM.step` calls them. As stated, this file alone proves gas formulas, not that execution charges those formulas. |
| `EvmYul/Yul/GasInterpreter.lean` | Disconnected from execution | `yulPrimOpDynamicGas`, memory expansion, and `consumeYulGas` are local gas-transition lemmas. Because `yulPrimOpDynamicGas` is not wired into `Yul/Interpreter.lean`, they do not establish that real Yul execution consumes the modeled gas. |
| `EvmYul/Yul/MessageCallCombinator.lean` | Disconnected environment-preparation model | `prepareChildCallEnv` proves preparation behavior for a pure environment constructor. It does not prove recursive call semantics, returndata behavior, gas forwarding, substate propagation, revert handling, or call-frame restoration. |
| `MetaSpecs/DialectCommutation.lean` | Partial genuine semantic theorem | The bridge through `effect` to real `EvmYul.step (.Yul)` and `EvmYul.step (.EVM)` is the strongest stated component. However, it covers only 14 shared instructions. It is a local commutation theorem, not whole-dialect equivalence, compiler correctness, or transaction-level equivalence. |
| `MetaSpecs/StateLensAlgebra.lean` | Mixed: genuine local theorem plus architectural duplication | `sstore_eq_storageLens` over actual `State.sstore` is a genuine semantic result. The duplicated `LawfulBEq UInt256`, `TransCmp`, and `LawfulEqCmp` instances are a serious coherence defect. They can create elaboration ambiguity, hide accidental representation mismatches, and make downstream theorem reuse unpredictable. |
| `MetaSpecs/GasTermination.lean` | Disconnected termination model | A decreasing `evmTerminationMeasure` under `consumeYulGas` and `L(g)` proves termination of those local functions. Since it is not connected to `EVM.step`, `Yul.step`, or their recursion, it does not prove interpreter termination. |
| `MetaSpecs/StaticCallAndRollback.lean` | Disconnected transactional model | `transactionalRollback_universal` by `rfl` over a local record update proves the behavior of `guardedTransition`/`resolveFrameTermination`. It does not prove rollback of actual `EVM.step` or `Yul.step`. This is a classic abstraction-gap theorem. |
| `Specs/GasSpec.lean` | Depends on theorem wiring | Potentially genuine if it proves the actual interpreter’s charged gas equals `EVM/Gas.lean`. Otherwise it is only a second gas model. The summary does not establish the required connection. |
| `Specs/YulEvmGasEquivalence.lean` | Likely partial or disconnected | A Yul/EVM gas equivalence theorem is meaningful only if both sides are instantiated with actual step relations and the same state/memory/storage observations. A pure formula equivalence is not execution equivalence. |
| `Specs/MessageCallSimulation.lean` | Open unless connected to recursive call execution | The existence of `MessageCallCombinator` does not establish simulation. The theorem must quantify over actual call transitions, child frames, gas, returndata, logs, storage, and rollback. |
| `Specs/ConformMultiFork.lean` | Pure configuration conformance unless execution-linked | A theorem that fork constants satisfy a table or monotonicity property is not evidence that all fork-specific branches in execution use the right fork. |
| `Specs/YellowPaperTraceability.lean` | Traceability metadata unless executable correspondence is proved | Naming or mapping formulas to Yellow Paper clauses is useful documentation. It is not a semantic proof unless each mapped rule is instantiated in the executable interpreter. |
| `Specs/PureKeccak256.lean` | Incomplete cryptographic specification | `roundConstants` and `rotl64` are components, not Keccak-f[1600], sponge absorption, padding, squeezing, or the EVM `KECCAK256` behavior. Any theorem claiming pure Keccak correctness from this module would be overstated. |
| `Specs/UInt256BitVecBridge.lean` | Potentially genuine representation bridge | This can be a real theorem if it proves equivalence between the exact `BitVec 256` operations and the exact operational UInt256 operations used by the interpreter. It must not silently bridge to Verity’s separate `Uint256`. |

### A.3 Verity modules

| Module | Classification | Assessment |
|---|---|---|
| `Verity/Core/Uint256.lean` | Separate semantic domain | It is not evidence about `EvmYul.UInt256` unless a proved representation/refinement bridge exists. Maintaining two canonical 256-bit types is currently a proof and code-generation boundary. |
| `Compiler/Autoresearch/GasCostModel.lean` | Disconnected duplicate gas model | Duplicated constants are not authoritative merely because `EvmYulGasAdapter.lean` bridges them post hoc. The adapter itself must prove equality for every fork, opcode class, warm/cold state, memory regime, and exceptional path. |
| `MaxwellGasSuperoptimizer.lean`: `GasOptimizationPassId` and `G1..G55` | Certificate registry, not verified optimization | Names and identifiers establish no transformation, no precondition, no target/source relation, and no cost improvement. |
| `g8..g55` arithmetic/boolean lemmas | Disconnected algebraic lemmas | These can be useful library lemmas, but they are not optimization correctness theorems unless quantified over actual IR/Yul expressions and linked to a pass. |
| 32 `burn` refutations | Disconnected or tautological arithmetic checks | `1 ≠ 2`, conditional simplifications, and `Nat` identities do not validate EVM arithmetic. EVM values are modulo `2^256`, division has EVM-specific semantics, and gas equivalence requires execution-context observables. |
| `validateSynthesizedSolcoreWitness` | Digest/equality stub | Comparing two pre-populated `SymbolicFunctionSummary` records with `decide (s = d)` validates only equality of supplied data. It does not synthesize, execute, type-check, refine, or independently verify a candidate. |
| `Compiler/Autoresearch/AccelPlugin.lean` | String allowlist and plugin metadata | `verifiedAccelTheoremAllowlist : List String` is not a proof registry. Strings are not theorem constants, pass implementations, or kernel-checked certificates. |
| `Profile.lean` and `defaultCertifiedPluginCatalog` | Catalog metadata | `G1..G55` in a catalog does not cause any pass to run. It is configuration, not certified acceleration. |
| `emitYulWithProfile` | Real compiler path, but currently not using the certified passes | The actual implementation path only runs `emitYulWithOptionsReport` and `applyTempReuseToObject`. Therefore the optimization catalog is not connected to emitted Yul. This is the most direct contradiction between architecture naming and runtime behavior. |
| `SolidityImport/Import.lean` and `EmitVerity.lean` | Heuristic translation | AST translation can be functional compiler code, but it is not verified lowering unless there is a source/target relation and a theorem covering the emitted result. Heuristics at this boundary enlarge the TCB substantially. |

### A.4 Severity summary

Blockers:

1. The certified optimizer is not on the `IRContract → ... → emitYul` path.
2. Gas charging is not connected from `GasInterpreter` to actual Yul execution.
3. Rollback and termination theorems target local models rather than actual interpreter transitions.
4. The Solcore witness validator checks equality of supplied summaries rather than validating a generated artifact.
5. The two UInt256 types and duplicate instances prevent a single coherent semantic domain.
6. Keccak is incomplete while the module structure suggests a cryptographic specification.

Important corrections:

1. `DialectCommutation` is a partial instruction-level theorem, not language equivalence.
2. `StateLensAlgebra.sstore_eq_storageLens` is meaningful, but the lens API is not yet fused with compiler storage locations.
3. Gas adapters should be treated as proof obligations, not compatibility glue.
4. String theorem allowlists and pass IDs should be labeled metadata until replaced by typed proof objects.

## (B) Prioritized improvement plan

### B.1 Priority 0: establish one executable semantic spine

Before adding more lemmas or optimization passes, define and enforce this path:

`Solidity/Verity source → AST → IRContract → typed optimization pass → Yul AST → emitted Yul → assembler validation → EVM/Yul semantics`

Every optimization theorem must sit between two actual IR/Yul representations. Every gas theorem must refer to the same execution semantics used by the interpreter.

The minimum acceptance criterion is not “the theorem compiles.” It is:

1. a source artifact;
2. the transformed artifact;
3. a relation between them;
4. a checker or theorem proving relation preservation;
5. actual emission of the transformed artifact;
6. differential execution or symbolic equivalence on the supported fragment.

### B.2 Gas performance: wire real passes into Codegen

Recommended order:

1. Introduce a typed `OptimizationPass` record:
   ```lean
   structure OptimizationPass where
     id        : PassId
     input     : IRContract → Prop
     transform : (c : IRContract) → input c → IRContract
     preserves  : ...
     gasBound   : ...
   ```
   Do not use string IDs as the identity.

2. Define `PassResult` with:
   - source IR;
   - target IR;
   - proof/certificate;
   - measured or statically computed gas bound;
   - diagnostics.

3. Make `emitYulWithProfile` execute the selected typed passes, not merely consult a catalog.

4. Add an explicit pass manifest generated from the implementation. The catalog must be derived from registered pass values, not maintained as an independent list.

5. For each G-pass, require:
   - an actual pattern matcher over `IRContract` or a typed sub-IR;
   - a transformation;
   - a side-condition checker;
   - a semantic-preservation theorem;
   - a gas comparison theorem;
   - a regression fixture showing the emitted Yul changed as intended.

6. Keep optimization domains separate:
   - `UInt256` algebra and bitvector simplification;
   - control-flow and boolean simplification;
   - storage/memory transformations;
   - gas-only scheduling or common-subexpression transformations.

Do not claim a gas optimization when only an algebraic identity is proved.

### B.3 Proof performance: turbo-lean, lean-native, BitVec

Use `BitVec 256` as the sole proof-facing arithmetic representation where possible.

Recommended technical direction:

1. Make `EvmYul.UInt256` a thin canonical wrapper around `BitVec 256`, with one constructor and one set of instances.
2. Prove operation lemmas once at the `BitVec` level.
3. Use `bv_decide` for closed or bounded bitvector goals.
4. Use normalization lemmas to expose arithmetic to `bv_decide`; do not force large `Fin (2^256)` arithmetic through general-purpose `Nat` automation.
5. Keep signed operations explicit:
   - unsigned interpretation;
   - signed interpretation;
   - conversion;
   - operation;
   - re-encoding.
6. Benchmark representative proofs under both `turbo-lean` and `lean-native`. Record:
   - elaboration time;
   - kernel checking time;
   - generated artifact size;
   - memory use;
   - axiom output.
7. Eliminate duplicate `LawfulBEq`, `TransCmp`, and `LawfulEqCmp` instances. Put all instances in the canonical UInt256 module and import them.
8. Avoid importing large optimizer modules into arithmetic proofs. The current 1,412-line `MaxwellGasSuperoptimizer.lean` is a likely elaboration and dependency hotspot.

The proof-performance target should be measured by proof families, not a single successful build:
- UInt256 arithmetic;
- gas formulas;
- state-lens lemmas;
- compiler pass preservation;
- end-to-end semantic simulation.

### B.4 TCB safety

#### 1. Close `SolcoreBridge`

The bridge needs a typed, checkable contract:

```lean
structure SolcoreCertificate where
  sourceIR    : IRContract
  targetYul   : YulProgram
  certificate : ...
  valid       : checkCertificate sourceIR targetYul certificate = true
```

The checker must inspect the actual source and target artifacts. A digest can identify an artifact, but digest equality cannot establish semantic validity.

Required gates:

- source IR hash matches the certificate;
- target Yul hash matches the emitted artifact;
- all referenced symbols and types resolve;
- certificate checker executes inside Lean or a separately audited checker with a narrow TCB;
- invalid certificates fail closed.

#### 2. Wire `GasInterpreter`

`evalPrimOp` and `step` must call the gas functions directly. Then prove:

```lean
theorem step_gas_accounting :
  step cfg s = some (s', event) →
  gasUsed event = yulPrimOpDynamicGas ... + memoryExpansion ...
```

The theorem must include exceptional paths, out-of-gas behavior, and fork parameters. A standalone `consumeYulGas` theorem is insufficient.

#### 3. Close `DialectCommutation`

Expand the relation from 14 instructions to a typed instruction coverage matrix. For each instruction, classify:

- exact semantic equality;
- equality under a state projection;
- equality with an environmental precondition;
- unsupported/open.

The theorem should quantify over actual step results, not only effects:

```lean
refines
  (EvmYul.step (.Yul) yulState)
  (EvmYul.step (.EVM) evmState)
```

The relation must specify memory, storage, transient storage, returndata, logs, gas, and exceptional outcomes.

#### 4. Assembler validation

Do not treat emitted Yul as the final artifact without validation. Add a deterministic validation phase that checks:

- parser acceptance;
- supported builtin set;
- opcode and dialect restrictions;
- jump destination/control-flow validity;
- stack-height or stack-safety constraints where applicable;
- calldata/returndata and memory conventions;
- source-to-emission symbol mapping;
- bytecode reproducibility.

If Solc remains outside the formal TCB, explicitly label the boundary: “verified Yul generation, unverified assembler/compiler backend.” If bytecode correctness is claimed, the backend needs its own evidence.

#### 5. Real termination and rollback

Lift the local theorems to actual transition relations:

- `EVM.step` decreases a well-founded measure on recursive call depth/fuel/gas;
- `Yul.step` uses the same measure where recursion is possible;
- rollback is proved over a call-frame transition before and after the actual child execution;
- successful calls commit the correct substate;
- revert/out-of-gas calls restore the checkpoint and preserve the specified returndata/status.

## (C) Surgical cleanup plan

### C.1 De-noise `MaxwellGasSuperoptimizer.lean`

Split it into four modules.

#### `Compiler/IR/Optimization/Pass.lean`

Owns:

- `PassId`;
- typed pass interfaces;
- source/target IR;
- side conditions;
- pass composition;
- pass diagnostics.

Replace `GasOptimizationPassId` with a typed enum whose constructors correspond only to implemented passes. Do not include G identifiers for unimplemented or purely planned work.

#### `Compiler/IR/Optimization/UInt256Lemmas.lean`

Owns:

- `BitVec 256` identities;
- signed/unsigned conversion lemmas;
- masking and truncation;
- division/modulo lemmas under explicit EVM preconditions;
- `bv_decide`-friendly normal forms.

These are reusable algebraic facts, not optimizer certificates.

#### `Compiler/IR/Optimization/GasPasses.lean`

Each pass gets its own file or small namespace:

```lean
namespace Pass.G08

def matches : IRExpr → Bool := ...
def rewrite : ...
theorem rewrite_sound : ...
theorem rewrite_gas_nonincreasing : ...
end Pass.G08
```

The theorem must mention the actual source and target expressions. A theorem over `Nat` should not be accepted as the pass theorem unless the IR operation is explicitly modeled by that `Nat` operation.

#### `Compiler/IR/Optimization/Certificate.lean`

Owns:

- certificate syntax;
- certificate checker;
- certificate-to-pass correspondence;
- rejection behavior;
- artifact hashes as identifiers only.

Delete or quarantine:

- `burn` refutations unrelated to an IR transformation;
- `if ts = ts` tautologies;
- standalone `Nat` identities;
- `decide (s = d)` summary comparisons.

They can live in a test or arithmetic scratch namespace, but must not be exported as certified optimizer evidence.

### C.2 Unify `EvmYul.UInt256` and `Verity.Core.Uint256`

Choose one canonical type. The better choice is the existing `EvmYul.UInt256` representation if it is already used by the executable EVM semantics:

```lean
abbrev Verity.Core.Uint256 := EvmYul.UInt256
```

If namespace isolation is required, use a type synonym only temporarily and prove explicit equivalence:

```lean
def Verity.Core.Uint256.toEvm : Uint256 → EvmYul.UInt256
def Verity.Core.Uint256.ofEvm : EvmYul.UInt256 → Uint256
theorem ofEvm_toEvm : ...
theorem toEvm_ofEvm : ...
```

Do not maintain two independent operation tables.

Migration sequence:

1. canonicalize constructors and projections;
2. move all instances to the canonical module;
3. replace downstream type annotations;
4. delete duplicate operation definitions;
5. add compatibility aliases temporarily;
6. remove aliases after all imports migrate.

Required invariant:

```lean
theorem verity_evm_uint256_operation :
  encodeVerity (verityOp x y) =
  evmOp (encodeVerity x) (encodeVerity y)
```

This must cover all operations used by the compiler, not only addition.

### C.3 Unify `EvmYul/EVM/Gas.lean` and `GasCostModel.lean`

Make `EvmYul/EVM/Gas.lean` the single source of truth for protocol gas constants and fork-dependent functions.

Define a semantic gas interface:

```lean
structure GasSchedule where
  fork : Fork
  sload : Warmness → Nat
  sstore : SstoreContext → Nat
  exp : ExpContext → Nat
  copy : CopyContext → Nat
  ...
```

Then:

```lean
def GasCostModel.forFork (f : Fork) : GasSchedule := ...
```

Verity should import or instantiate this schedule, not duplicate constants.

If a compiler-specific cost model is needed, distinguish it clearly:

```lean
structure StaticGasEstimate where
  lowerBound : Nat
  upperBound : Nat
  sound : ...
```

The compiler estimate may be conservative or symbolic, but it must not shadow protocol constants.

The adapter should be reduced to a proved identity theorem:

```lean
theorem adapter_matches_evm_schedule :
  EvmYulGasAdapter.cost op ctx =
  GasSchedule.cost fork op ctx
```

Test matrix:

- every supported fork;
- warm/cold access;
- zero/nonzero storage transitions;
- memory expansion boundaries;
- exponent byte length;
- copy word rounding;
- logs and topic counts;
- intrinsic transaction gas;
- exceptional and out-of-gas cases.

### C.4 Fuse `StateLens`, `StorageLoc`, and `SpecStorageKey`

Create one canonical storage-location abstraction:

```lean
structure StorageLoc where
  account : Address
  slot    : UInt256
  domain  : StorageDomain
```

where `StorageDomain` distinguishes persistent storage and transient storage.

Define:

```lean
def SpecStorageKey := StorageLoc
```

or, if a specification key must be abstract:

```lean
structure SpecStorageKey where
  loc : StorageLoc
  abstraction : ...
```

Then make `StateLens` parameterized by `StorageLoc`:

```lean
structure StateLens (σ α) where
  get    : σ → α
  set    : σ → α → σ
  get_set : ...
  set_get : ...
```

Canonical lenses:

```lean
def storageLens    : State → StorageLoc → UInt256 → State
def transientLens  : State → StorageLoc → UInt256 → State
def accountMapLens : ...
def substateLens   : ...
```

The important point is that the lens must identify the same location used by:

1. `State.sstore`;
2. compiler `StorageLoc`;
3. specification `SpecStorageKey`;
4. emitted Yul storage access.

Required theorems:

```lean
theorem sstore_lens_agrees :
  State.sstore s account slot value =
  storageLens.set s ⟨account, slot, .persistent⟩ value
```

```lean
theorem spec_key_compiles_to_same_slot :
  compileStorageKey k = k.loc.slot
```

```lean
theorem emitted_sstore_refines_lens :
  execYul (emitSstore loc value) s =
  storageLens.set s loc value
```

For mappings and dynamic slots, split the abstraction:

- logical key;
- slot derivation;
- concrete 256-bit slot;
- state lens.

Prove slot derivation separately. Do not hide `keccak256` slot computation inside a generic lens theorem.

## Recommended execution order

1. Remove duplicate UInt256 instances and choose the canonical UInt256 type.
2. Make `EvmYul/EVM/Gas.lean` authoritative and delete duplicated Verity constants.
3. Wire `GasInterpreter` into actual `Yul.step`.
4. Replace string pass catalogs with typed pass records.
5. Connect one complete optimization pass through IR to emitted Yul.
6. Replace `validateSynthesizedSolcoreWitness` with an artifact-bound checker.
7. Fuse storage locations and lenses.
8. Expand dialect commutation and rollback over actual transitions.
9. Add assembler validation and explicit backend TCB documentation.
10. Only then classify the resulting system as a verified optimizing compiler.

The decisive acceptance criterion is end-to-end reachability: a theorem must be reachable from the artifact that the compiler actually emits. At present, the strongest parts are the UInt256 substrate, the local `State.sstore` lens theorem, and the 14-instruction dialect bridge. The gas interpreter, optimizer certificates, rollback, termination, and acceleration catalog are not yet connected strongly enough to support system-level verification claims.
