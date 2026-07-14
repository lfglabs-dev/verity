# Trust Assumptions and Verification Boundaries

This document states what Verity proves and what it still trusts.

## Compilation Pipeline

```
EDSL (Lean)
  ↓ [Layer 1: PROVEN FOR CURRENT CONTRACTS, generic core, contract bridges]
CompilationModel
  ↓ [Layer 2: SUPPORTED-FRAGMENT GENERIC THEOREM -- CompilationModel → IR]
IR
  ↓ [Layer 3: GENERIC SURFACE, explicit bridge hypothesis, IR → Yul]
Yul
  ↓ [trusted: solc]
EVM Bytecode
```

The repository currently has 0 `sorry` placeholders across the `Compiler/**/*.lean` and `Verity/**/*.lean` proof modules that participate in the verified compiler stack. Layer 2 (Source → IR) and Layer 3 (IR → Yul) proof scripts are fully discharged, and it now has 0 documented Lean axioms. See [AXIOMS.md](AXIOMS.md) for details. Audit evidence and generated trust-boundary artifacts are indexed in [AUDIT.md](AUDIT.md).

## What's Verified

- **Layer 1**: A generic typed-IR compilation-correctness core exists, but the active contract-level bridges are still instantiated per contract and internal-helper proof reuse is not yet a first-class generic interface.
  This names the frontend EDSL-to-`CompilationModel` bridge only; the
  contract-specific specification theorems in `Contracts/<Name>/Proofs/` are a
  separate proof layer about human-readable contract behavior.
- **Layer 2**: A generic whole-contract theorem is proved for the current supported `CompilationModel` fragment. `supported_function_correct` is now a real theorem, the initial-state normalization step is proved, the former generic body-simulation axiom has been eliminated, and the theorem surface makes explicit that the observed transaction-context fields must already be normalized to the bounded source-side `Address`/`Uint256` domains. Remaining Layer 2 work is now about widening the supported fragment and helper-aware completeness, not repairing `sorry` placeholders.
- **Layer 3**: IR → Yul preservation is generic at the proof surface, and the remaining dispatch bridge now lives as an explicit theorem hypothesis rather than a Lean axiom. The checked contract-level theorem surface makes the dispatch-guard safety preconditions explicit: non-payable cases must see word-level zero `msg.value`, and each selected function case must have a non-wrapping calldata-width guard.

Current theorem totals, property-test coverage, and proof status live in [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md).

## Trusted Components

### 1. Solidity Compiler (`solc`)
- **Role**: Compiles Yul → EVM bytecode.
- **Version**: 0.8.33+commit.64118f21 (pinned).
- **Mitigation**: CI enforces pin and Yul compileability checks.

### 2. Lean Axioms
- **Role**: Bridge remaining proof obligations not yet fully discharged.
- **Status**: 0 documented axioms in [AXIOMS.md](AXIOMS.md). The mapping-slot range axiom has been eliminated via the kernel-computable Keccak engine. Selector computation is kernel-computable, the Layer 2 generic body-simulation axiom has been eliminated, and the Layer 3 dispatch bridge remains an explicit theorem hypothesis rather than a Lean axiom.
- **Mitigation**: CI axiom reporting and location checks enforce explicit tracking.

### 3. Keccak-based Selector Computation
- **Role**: Function selector derivation (`bytes4(keccak256(signature))`).
- **Status**: kernel-computable in `Compiler/Selectors.lean` via the vendored unrolled Keccak engine in `Compiler/Keccak/`.
- **Mitigation**: CI cross-checks against `solc --hashes`, selector fixtures, and fixed selector examples.

### 4. Linked Yul Libraries
- **Role**: External functions injected at compile time (e.g., Poseidon hash).
- **Trust**: Semantic correctness of linked code. Compiler validates names, arities, collisions.

### 5. Mapping Slot Derivation
- **Role**: `keccak256(abi.encode(key, baseSlot))` for Solidity-compatible storage (`activeMappingSlotBackend = .keccak`).
- **Trust**: external keccak implementation (`ffi.KEC` via EVMYul FFI) + standard collision-resistance assumptions (same trust class as Solidity/EVM).
- **Mitigation**: Abstraction-boundary CI, selector/hash cross-checks.
- **Audit surface**: machine-readable trust reports now emit the explicit primitive assumption `keccak256_memory_slice_matches_evm` whenever a contract uses `Expr.keccak256`.
- **Source-semantics realization**: the executable source interpreter
  (`Compiler/Proofs/IRGeneration/SourceSemantics.lean`) now evaluates
  `Expr.keccak256 offset size` via `keccakMemorySlice` — reading word-aligned
  `RuntimeState` memory, concatenating big-endian, truncating to `size`, and
  hashing with the in-tree `KeccakEngine.keccak256` (previously it returned
  `none`/revert). The trust assumption `keccak256_memory_slice_matches_evm` is the
  word-aligned-access faithfulness of that memory slice; the model is word-keyed
  and does not represent sub-word memory aliasing. See AXIOMS.md
  "Kernel-computable source-semantics `keccak256(offset, size)`".

### 6. EVM/Yul Semantics and Gas
- **Role**: Runtime execution model.
- **Status (native transition complete)**: native builtin dispatch lives in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBuiltinSemantics.lean` and `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeLowering.lean`; `EvmYulLeanBridgeLemmas.lean` records native routing facts for the 36 covered builtin cases, including 25 universal pure bridge theorems. All pure bridge cases are now covered by universal symbolic lemmas. The legacy runtime-oracle stack and builtin comparison oracle have been removed as part of the EVMYulLean transition (DoD-5). The public EndToEnd composition surface in `Compiler/Proofs/EndToEnd.lean` targets native `EvmYul.Yul.callDispatcher` execution through `Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness`: the public surface is `nativeResultsMatchOn`, `sourceResultMatchesNativeOn`, the source/native result-composition theorem over that native result surface, and the concrete SimpleStorage native theorem. The fuel-indexed `nativeIRRuntimeMatchesIR` seams are file-local. Gas is not modeled.
- **Trust boundary (EVMYulLean EndToEnd target)**: For the native EndToEnd path, the runtime authority is EVMYulLean dispatcher execution after Verity Yul is lowered by the native harness and projected onto the observable result surface. There is no longer a legacy preservation/equivalence stack; only the native chain remains.
- **Fork dependency**: Verity pins [`lfglabs-dev/EVMYulLean`](https://github.com/lfglabs-dev/EVMYulLean), a fork of [`NethermindEth/EVMYulLean`](https://github.com/NethermindEth/EVMYulLean). The pinned commit is recorded in `lake-manifest.json` under the `evmyul` package. The exact divergence from upstream is enumerated in [`artifacts/evmyullean_fork_audit.json`](artifacts/evmyullean_fork_audit.json), regenerated by `scripts/generate_evmyullean_fork_audit.py` and validated by `make check`. As of the current pin, the fork is 2 commits ahead of `upstream/main` and 0 behind; both commits are non-semantic (one visibility change on an exponentiation accumulator, one Lean 4.22.0 deprecation fix), so upstream Ethereum conformance test coverage applies transitively. In addition to the `make check` validation, a weekly scheduled GitHub Actions workflow ([`.github/workflows/evmyullean-fork-conformance.yml`](.github/workflows/evmyullean-fork-conformance.yml)) runs `make test-evmyullean-fork`, which re-verifies the fork audit artifact against `lake-manifest.json`, checks the EVMYulLean native lowering report, rebuilds the native transition harness, rebuilds the public EndToEnd EVMYulLean target, and rebuilds the native builtin routing lemmas together with the native bridge smoke tests and 0 concrete bridge tests, surfacing any upstream drift as a red workflow plus an automatically opened or updated GitHub issue for scheduled/manual failures.
- **Remaining gap for whole-program retargeting**: The public EndToEnd native surface is in place, but the per-`BridgedStraightStmt` IR↔native observation-equivalence framework that would land truly unconditional S1–S8 / F2/F4/F6/F7 / true S8 has not been built yet — that work is multi-week and tracked separately. The external-call/function-table family now has function-table-aware closure scaffolding in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanCallClosure.lean` (per-family source-level predicates, per-family `compileStmt`/`compileStmtList` closure theorems, `ECMBridgeable` per-module obligation, and a `BridgedStmts`-preserving `pfx ++ sfx` composition lemma); end-to-end wiring through `SupportedFragment`/`SupportedSpec` for whole contracts using these constructors is the next milestone.
- **Implication**: Semantic correctness does not imply gas-safety.
- **Proxy note**: `delegatecall`-based proxy / upgradeability flows still sit outside the current native verified runtime model. Archive `--trust-report` and use `--deny-proxy-upgradeability` when proxy semantics must remain outside the selected verified subset (issue `#1420`).

### 7. External Call Modules (ECMs)
- **Role**: Reusable typed external call patterns (ERC-20 writes/reads including `totalSupply`, ERC-4626 preview/conversion helpers plus `totalAssets`, `asset`, `max*` limit reads, and `deposit`, oracle reads, precompiles 0x01 / 0x02 / 0x06 / 0x07 / 0x08 — `ecrecover`, `sha256`, BN254 `bn256Add`, `bn256ScalarMul`, `bn256Pairing` — callbacks, and same-contract `selfDelegateMulticallBytes`).
- **Trust**: Each module's `compile` produces correct Yul. Bug in one module doesn't affect others. `selfDelegateMulticallBytes` is an explicitly trusted ECM boundary under `self_delegate_multicall_bytes_revert_bubbling`: the compiler emits concrete bounds checks for ABI element offsets, including a pre-add overflow guard before forming the calldata head offset, but full non-empty multicall revert-bubbling semantics are not yet machine-proven.
- **Mitigation**: Axiom aggregation at compile time (`--verbose`), machine-readable trust-surface emission via `--trust-report <path>`, and a fail-closed verification gate via `--deny-unchecked-dependencies` when unchecked foreign surfaces must be excluded. See [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md).
- **Caller-frame preservation**: The EVM frame condition (external `CALL` cannot mutate caller storage / transient storage / memory outside the declared output buffer) is now a *theorem* of `Verity.EVM.Frame` rather than an assumption. Downstream proofs consume `external_call_preserves_caller_storage` etc. directly. The abstract memory model used by these theorems is `Verity.EVM.MemoryModel`; the solc memory-layout schema and call-buffer-disjoint-from-heap result are in `Verity.EVM.Layout`. EvmYul ↔ abstract-model correspondence remains the open follow-up.

### 8. Lean Kernel
- **Role**: Proof checker soundness. Foundational assumption for all Lean-based verification.
- **Lean 4.24 string-reduction boundary**: The closed scratch-name facts
  `Compiler.CompilationModel.compatScratch_startsWith_reserved` and
  `Compiler.CompilationModel.compatScratch_not_internalImmutable` use
  `native_decide`. Their printed proof dependencies add `Lean.ofReduceBool` to
  downstream consumers; the reduction also implicitly trusts Lean's native
  compiler (`Lean.trustCompiler`), although that builtin does not occur in the
  current `#print axioms` terms. They are kept in
  the dedicated non-proof module
  `Compiler/CompilationModel/ReservedScratchNames.lean`: Lean 4.24 makes the
  recursive `String.startsWith` worker private and provides no public
  correctness theorem. This boundary should be removed as soon as Lean or
  Batteries supplies `substrEq`/`startsWith` correctness lemmas.

### 9. Macro Elaborator (`verity_contract`)
- **Role**: Generates both EDSL `Contract` monad value and `CompilationModel` from one syntax tree.
- **Status**: Trusted unverified metaprogram ([Verity/Macro/Translate.lean](Verity/Macro/Translate.lean)).
- **Risk**: A translation bug would silently cause EDSL and CompilationModel to diverge.
- **Mitigation**: The generic Layer 2 whole-contract theorem, macro-generated `_semantic_preservation` body-alignment checks, and differential tests catch divergence on the current contract set.

### 10. Local Unsafe / Refinement Obligations
- **Role**: Let a function or constructor declare a localized proof obligation for an unsafe/assembly-shaped boundary without marking the whole contract as opaque.
- **Status**: Surfaced explicitly in `--trust-report`, `--verbose`, and `proofStatus.*.localObligations`.
- **Mitigation**: `verity-compiler --deny-local-obligations` fails closed on any obligation that remains `assumed` or `unchecked`.

### 10a. Raw Yul Escape Hatch
- **Role**: Model ad-hoc handwritten Yul through `Stmt.unsafeYul` and
  `UnsafeYulFragment` when the surface is only a single instruction or otherwise
  too local to justify a first-class `Stmt` constructor.
- **Status**: Raw Yul fragments lower through the single
  `unsafeYulToEVMYul` bridge and carry their own mechanics, termination
  metadata, and local obligations. Raw memory reverts use
  `UnsafeYulFragment.rawRevert` through `Stmt.unsafeYul`.
- **Mitigation**: Keep common typed primitives such as `mstore` and
  `calldatacopy` first-class only when Verity has stable semantics and they are
  useful for proofs. Treat other raw Yul as an explicit trust-report surface,
  and use `--deny-local-obligations` / low-level deny gates for strict builds.
- **Reference**: See [docs/LOW_LEVEL_YUL.md](docs/LOW_LEVEL_YUL.md).

### 11. Consumer-Declared Intrinsics
- **Role**: Let downstream packages bind a source-level Verity function to a
  target EVM opcode or Yul builtin without adding opcode-specific code to
  Verity. The first use case is Tamago's EIP-7939 `CLZ` binding, which lowers
  to `verbatim_1i_1o(hex"1e", x)`.
- **Trust**: While an intrinsic obligation is `assumed`, the consumer owns the
  claim that the declared Lean `semantics` matches the emitted opcode on the
  selected chain fork. The declaration records the obligation in the consumer
  namespace next to the generated semantic wrapper, and the consumer must
  document it in its repository rather than treating it as a Verity project-level
  axiom.
- **Status**: This change introduces a generic intrinsic lowering path and
  keeps Verity's own `AXIOMS.md` at zero project-level axioms.
  `min_fork` checks are enforced against the compiler target fork, defaulting
  to Cancun because the pinned EVMYulLean fork declares
  `EvmYul.TargetSchedule := "Cancun"`. Machine-readable intrinsic trust-report
  entries remain follow-up hardening. The Verity-owned proof fragment now
  covers intrinsic argument scope accounting, generic verbatim/builtin lowering
  shape, fork-order facts, arity rejection, and fail-closed exclusion from the
  current end-to-end proven fragment; it does not assert any opcode semantics.
- **Mitigation**: Audit every `verity_intrinsic` declaration in consumer code.
  Check opcode bytes, fork requirement, semantic edge cases, and the obligation
  status. Fork enforcement is fail-closed: a contract targeting a fork lower
  than an intrinsic's `min_fork` errors unless
  `--allow-future-fork-intrinsics` is passed.
- **Reference**: See [docs/INTRINSICS.md](docs/INTRINSICS.md).

## Semantic Caveats

### Wrapping Arithmetic
`Uint256` arithmetic is **wrapping modulo 2^256**, matching the EVM. This is proven, not assumed (see `Compiler/Proofs/ArithmeticProfile.lean`). Checked operations (`safeAdd`, `safeSub`, `safeMul`) are available for overflow protection. See [docs/ARITHMETIC_PROFILE.md](docs/ARITHMETIC_PROFILE.md).

### Revert-State Modeling
High-level semantics can expose intermediate state in reverted computations. EVM reverts discard state. Contracts should use checks-before-effects. See [docs/REVERT_STATE_MODEL.md](docs/REVERT_STATE_MODEL.md).

### Reentrancy Guard (`nonreentrant(lockField)`)
Functions annotated `nonreentrant(lockField)` are compiled with a
**transient-storage** reentrancy guard prologue (#1893): an
`if eq(tload(lockSlot), 1) { revert(0, 0) }; tstore(lockSlot, 1)` pair runs
before any user-authored Yul. Transient storage (EIP-1153, Cancun+) auto-clears
at end-of-transaction, so the guard does not need an explicit release path —
early `return`, `revert`, or panic cannot leak the lock across transactions.
The guard exempts the function from CEI ordering enforcement, so state writes
after external calls are permitted within reentrancy-protected entry points.
**Fork requirement**: the compile driver rejects any contract carrying a
`nonreentrant(<lock>)` annotation when the targeted EVM fork predates
Cancun (the `validateNonReentrantForkCompatibility` pre-check in
`Compiler.CompilationModel.Dispatch`); on pre-Cancun chains the synthesised
TLOAD/TSTORE opcodes would not be available, so silently emitting them
would leave the post-external-call reentry window open while validation
still treated the function as CEI-exempt (#1968). Either raise the target
fork to Cancun+ or drop the annotation; manual reentrancy guards (e.g.
SSTORE-based) on pre-Cancun chains remain the caller's responsibility.
Trust boundary: the guard's correctness reduces to EVM TLOAD/TSTORE
semantics (already in the trusted EVM target) plus the macro-level invariant
that the lock field is a scalar `uint256` storage field used solely by the
guard. Guarded functions sit outside `SupportedSpec` in this version, and
this boundary is now machine-checked rather than prose-only: the
`SupportedFunction.noNonReentrant` field (`fn.nonReentrantLock = none`)
makes any attempt to include a guarded function in the proven fragment a
type error, and `ContractShape.guardedFunctionsMapM_eq` discharges the
guard attachment as the identity on the lock-free fragment. Proof-side
guard preservation lemmas (modelling the TLOAD/TSTORE prologue itself)
remain deferred follow-up work.

### Reentrancy Rely-Guarantee Framework (`Verity.Core.Reentrancy`)
A proof-level companion to the runtime `nonreentrant` guard above. Where the
guard *prevents* reentry at runtime (transient storage), this framework lets an
author *prove* that reentry — even when permitted — cannot break a declared
global invariant `I : ContractState → Prop`.

- **What it adds (all additive, all proven in-kernel)**:
  - `Verity.Core.Invariant` — a state-polymorphic rely-guarantee library
    (`Preserves`, `runSeq`, `runSeq_preserves`); no imports, no axioms.
  - `Verity.Core.Reentrancy` — grounds the library against the real
    `ContractState`/`Contract` monad: `reentrantCall` (adversarial reentry as a
    `Contract Unit` effect), `ContractPreserves`, and `ReentrancySpec` (a global
    invariant + entrypoint registry + one preservation obligation per
    entrypoint). The meta-theorem `ReentrancySpec.schedule_preserves` discharges
    the *entire* adversarial interleaving space from those per-entrypoint
    obligations — no interleaving enumeration.
  - `Env.reenter` — a hook on `Env` (default `id`, the no-reentry case) so the
    adversary transformer threads through semantics like any other effect.
  - A forward-compatible multi-contract layer (`System` / `lift` / `Isys` /
    `cross_contract_schedule_preserves`) that reuses the same library at
    `σ := System` with no single-contract proof redone.
- **Proven, not assumed**: every theorem closes in the Lean kernel
  (`decide` / structural induction); the framework adds **zero project-level
  axioms** and uses no `native_decide`. The Midnight `take`/`liquidate` worked
  example (`Contracts/ReentrancyRelyGuarantee`) machine-checks both that the
  no-lock `take` admits a permanent bad-debt liquidation and that the locked
  `take` admits none for any lock-respecting adversary.
- **Trust boundary (author obligations)**:
  1. **Registry completeness** — `ReentrancySpec.entrypoints` must list *every*
     externally reachable state transformer an adversary can invoke during a
     reentry window. Omitting a reachable entrypoint voids the guarantee
     (analogous to declaring the lock field for `nonreentrant`). The
     macro-emitted entrypoint registry is the intended source of this list; until
     that emission lands, the list is author-supplied.
  2. **Adversary-model fidelity** — reentry is modeled as an arbitrary
     `ContractState → ContractState` over *this* contract's persistent channels
     (`adv` in `reentrantCall`). This captures self- and cross-contract reentry
     that affects only this contract's storage. It does **not** model, in this
     version: unbounded mutual A↔B recursion, or read-only / oracle-return-value
     precision. Those are explicit `System`-layer follow-ups.
  3. **Invariant adequacy** — the safety claim is only as strong as the chosen
     invariant `I`. The lock-as-disjunct idiom (`I s := healthy s ∨ locked s`)
     is the recommended pattern for trade-window safety, but `I` itself is
     author-chosen and not verified against any external specification.
- **Reference**: [Verity/Core/Reentrancy.lean](Verity/Core/Reentrancy.lean),
  [Contracts/ReentrancyRelyGuarantee/Contract.lean](Contracts/ReentrancyRelyGuarantee/Contract.lean).

### Cross-Function Reentrancy Gate (fail-closed)
Every function whose body opens a reentrancy window (`externalCallBind`,
`tryExternalCallBind`, a state-changing `call`-summarised `ecm`, a non-builtin
`externalCall` expression, or an `unsafeYul` fragment carrying an external-call
mechanic) and that is **not** `view`/`pure` must declare a reentrancy
disposition or compilation fails (`validateReentrancyDisposition`, keyed on
`stmtOpensReentrancyWindow`, in
[Compiler/CompilationModel/Validation.lean](Compiler/CompilationModel/Validation.lean)).
This is a dedicated pass that runs *after* call well-formedness validation, so a
malformed external call surfaces its structural error first and the reentrancy
policy only judges otherwise well-formed calls. It is also independent of the
single-function CEI check (in `validateFunctionSpec`), which runs earlier in the
per-function pipeline; a CEI-violating function is therefore rejected by the CEI
check before this gate is consulted.
An external call hands control to an untrusted callee that may re-enter a
*different* entrypoint while this contract's state is mid-update — the Midnight
`take`/`liquidate` class of bug. Single-function CEI ordering does **not**
prevent this, so `cei_safe` and `allow_post_interaction_writes` are
intentionally **not** accepted by this gate; only the two dispositions below
are:

- `nonreentrant(<lock>)` — synthesises the runtime transient-storage guard
  documented above (#1893), closing the window at the external-dispatch
  boundary. Sound by construction (reduces to TLOAD/TSTORE semantics).
- `reentrancy_trusted` — a **metadata-only, unproven author assertion** that
  every external callee reachable from this function is trusted not to re-enter.
  It emits no code and carries no proof obligation: it is a recorded trust
  boundary, the audited opt-out for functions whose external targets are
  known-safe (e.g. a hard-coded protocol-owned contract) or which run in a
  context where no exploitable reentry exists. The author owns this assertion;
  the compiler does not verify it. `view`/`pure` functions need no disposition
  because a read-only (`staticcall`) context cannot mutate state and so cannot
  open a state-corrupting reentry window.

For the same EVM-static-context reason, a `staticcall`-summarised External Call
Module (`ecm` whose `summaryMutability = .staticcall`: precompiles such as
`sha256`/`bn256`, `keccak`, ABI-encoding helpers, and view-only cross-contract
reads) is **not** treated as window-opening and needs no disposition — any
state-mutating opcode in the callee reverts under STATICCALL. Only a
state-changing `call`-summarised ECM (e.g. an ERC-20 transfer) is gated. This
keeps the gate precise rather than flooding hash/precompile-using contracts with
vacuous `reentrancy_trusted` tags.

Trust boundary: a `reentrancy_trusted` annotation is exactly as strong as the
author's audit of the called targets — it is the reentrancy analogue of trusting
a linked Yul library. The gate guarantees only that *no* external-call function
silently ships without a disposition; it does not, for `reentrancy_trusted`,
prove the assertion. Functions carrying a proof-level guarantee should instead
use the rely-guarantee framework above and/or the `nonreentrant` runtime guard.

Internal-call interaction: the `nonreentrant(<lock>)` guard is synthesised
**only** at the external dispatch boundary (`attachNonReentrantGuard`, #1893), so
its protection does not survive on the internal-helper *shadow* the macro emits
for direct intra-contract calls (the shadow drops the lock to avoid
double-guarding the already-guarded public chain). Consequently a *lock-only*
`nonreentrant(<lock>)` function (one that does **not** also carry
`reentrancy_trusted`) **cannot be invoked as an internal helper**: such a call is
rejected at macro lowering (`ensureCallableAsInternalHelper`,
[Verity/Macro/Internal.lean](Verity/Macro/Internal.lean)), because routing it
through the lock-free shadow would run the guarded body without the lock and
silently bypass the only reentrancy protection it had. Calling a function that
*also* carries `reentrancy_trusted` is accepted — that disposition is a global
author assertion covering every entry path, including the lock-free internal one.
This mirrors the parse-time rejection of an `internal nonreentrant(<lock>)`
helper (`NonreentrantInternalHelperRejected`, #1971).

- **Reference**: [Compiler/CompilationModel/Validation.lean](Compiler/CompilationModel/Validation.lean)
  (`validateReentrancyDisposition`, the cross-function reentrancy gate — a
  dedicated pass run after call well-formedness, distinct from the
  single-function CEI check in `validateFunctionSpec`);
  [Verity/Macro/Internal.lean](Verity/Macro/Internal.lean)
  (`ensureCallableAsInternalHelper`, the lowering-time rejection of internal
  calls to lock-only `nonreentrant` entries).
- **Regression evidence**: [Contracts/Smoke/SecurityCombos.lean](Contracts/Smoke/SecurityCombos.lean)
  pairs `ReentrancyDispositionRequired` (a CEI-clean `take` rejected by the gate,
  asserted via `#guard_msgs`) with `ReentrancyDispositionDeclared` (the identical
  body accepted once it carries `reentrancy_trusted`) — the Midnight
  `take`/`liquidate` shape cannot pass `#check_contract` undeclared. The
  internal-helper rule is pinned by `NonreentrantCalledAsInternalHelperRejected`
  (a public `nonreentrant` entry called from another body, rejected at lowering)
  and `NonreentrantTrustedInternalHelperAccepted` (the same call accepted once the
  callee adds `reentrancy_trusted`).

## Security Audit Checklist

1. Confirm deployment uses the supported EDSL CLI path.
2. Review [AXIOMS.md](AXIOMS.md); ensure the axiom list is unchanged and justified.
3. If linked libraries are used, audit each linked Yul file as trusted code.
4. Validate selector, Yul compile, and storage-layout CI checks.
5. Confirm arithmetic and revert assumptions are acceptable for the target contract.
6. Review the low-level mechanics / external assumption report (`--verbose`) and archive `--trust-report <path>` for audit evidence when external calls or linked externals are used. For verification-oriented builds, also pass `--deny-unchecked-dependencies` so any remaining unchecked foreign surface fails closed.

## Planned Hardening

- **Issue #967**: Proof-carrying Yul rewrite rules, versioned parity packs, AST identity gates.
- **Issue #998**: Per-function machine-checked `EDSL execution ≡ EVMYulLean(compile(CompilationModel))` theorems.

## Related Documents

- [AUDIT.md](AUDIT.md) | [AXIOMS.md](AXIOMS.md) | [docs/INTRINSICS.md](docs/INTRINSICS.md) | [docs/ARITHMETIC_PROFILE.md](docs/ARITHMETIC_PROFILE.md) | [docs/REVERT_STATE_MODEL.md](docs/REVERT_STATE_MODEL.md)
- [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md) | [docs/ROADMAP.md](docs/ROADMAP.md) | [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)

---

**Last Updated**: 2026-05 (intrinsics addition)
**Maintainer Rule**: Update on every trust-boundary-relevant code change.
