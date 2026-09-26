# Trust Assumptions and Verification Boundaries

This document states what Verity proves and what it still trusts.

## Solidity import

`Compiler/SolidityImport/Import.lean` selects functions from a solc project,
closes over the definitions solc's declaration ids actually reach, and elaborates
a `CompilationModel` (see `docs/SOLIDITY_IMPORT.md`). Execution of an accepted import is
`Compiler.CompilationModel.Denote.execStmt`, restricted by
`stmtListCovered` in `Compiler/SolidityImport/Coverage.lean`. That predicate is
not `SupportedFunction`: the slice uses `panic`, `returnValues`, packed
`structMember` / `structMember2`, and checked arithmetic, which the IR raccord
does not cover. `DenoteAgreement.execStmt_eq` still holds, including
`Stmt.returnValues`, which records source-order words on `DenoteState` and
finishes as `.stop`. `Stmt.panic` and resolved `Stmt.panicCode` retain their
36-byte ABI payload in `StmtOutcome.revertWithData`; statement lists and loops
propagate those bytes. The agreement projection explicitly erases them to the
older SourceSemantics result, so that theorem does not establish byte equality.
The differential runner compares the bytes on all three routes and treats a
payload-free Denote failure as an instrumentation error. Legacy scalar accessors
still expose only success versus failure. The call-composition interface retains
local panic bytes separately from its legacy word-return result; full byte-level
external-call composition is not yet certified.

Literal-message `require` retains the exact ABI `Error(string)` payload,
including UTF-8 byte length and padding. The importer checks solc's resolved
builtin signature and literal bytes; dynamic messages are rejected. Denote
also encodes declared static scalar custom errors with a unique declaration,
matching arity and canonical arguments. Imported custom-error `require` calls
accept only decimal numeric literals or scalar-binding arguments; general expressions are
rejected until their evaluation order, including competing panics, is covered.
Explicit `revert CustomError(...)` statements remain outside the importer. Error
declarations travel with the execution state. The differential oracle computes
signature Keccak over a temporary word-chunk memory buffer; this does not
establish general Solidity memory or ABI-decoder correctness. The legacy
agreement projection continues to erase rich revert bytes.

The experimental stateful instrument in `scripts/solidity_differential` runs
separate real Anvil transactions against solc and Verity bytecode, and invokes
`SequenceRunner` for Denote. Its scalar trace calls the actual statement
executor; `traceStraightLine_agrees` proves equality of the complete outcome,
including the resulting world and rich revert bytes, whenever tracing succeeds.
The transaction wrapper clears transient storage and frame-local observations,
commits successful execution, and restores the initial world on rich reverts.
Unsupported statements, foreign storage observations and value transfers fail
the scalar adapter. Named events with uint256 parameters are encoded from the
actual Denote emission and the model declaration: signature Keccak topic, indexed
word topics, and unindexed word data. The current executor retains emission
arguments in source order, so the observation layer partitions them using the
declaration. Unknown or ambiguous declarations, arity mismatches, other parameter
types and more than three indexed arguments fail explicitly. Anonymous events
and foreign emitters are outside this instrument. No synthetic event or revert
observations fill unsupported gaps.

Storage comparison samples the cumulative union of accessed slots after every
transaction using fresh discovery and replay worlds. The EVM access inventory
and observations trust Foundry's call/prestate tracers and historical storage
RPC. Calldata and model arguments are paired by the campaign generator; this
is not a proof of ABI decoding or dispatch. The handwritten sequence fixture
is an instrument test, not evidence of additional importable Solidity. Mock
ERC20/oracle/callback tests currently validate only the EVM adapter; their
Denote external-world counterparts remain an integration obligation. Sequence
reduction proves deletion-1-minimality by replay within its stated budget,
not global minimality of arguments or programs.

The imported `EnvironmentSequence` fixture additionally exercises multiple entry
points and the dedicated caller, current-contract, timestamp, block-number, and
chain-id expressions. Solc builtin declaration ids and type identifiers select
these lowerings; names alone do not identify a builtin. The stateful harness
provides the same transaction context to each route and compares returned ABI
bytes. Direct, local-binding, and helper variants are separately imported and
checked for identical observations. This remains sampled differential evidence,
not a proof of frontend correctness. Payable entry points and unsupported context
members fail import rather than inheriting incomplete value-transfer behavior.
The campaign identity includes the actual imported Solidity fixture alongside
the Lean driver and implementation artifacts, detecting local source edits or
removal during replay. It does not defend against a malicious filesystem.

The imported scalar storage slice trusts solc's slot/byte-offset layout and the
importer's conversion to packed bit ranges. Unsigned integers, addresses and
bytes32 are represented by physical uint256 fields; their source types govern
casts and ABI results. Writes and deletes use the existing masked Denote write
semantics. The imported packed-storage sequence supplies sampled A/B/C evidence,
including rollback and sibling retention, not a frontend equivalence theorem.
Write-aware coverage does not extend the old read-only preservation theorem.
Separate kernel-checked frame lemmas cover other persistent slots, not arbitrary
contract invariants. Void root fallthrough uses the compiler's dedicated stop instruction. Denote
records an explicit-stop marker separately from the legacy return-word
projection. The transaction adapter emits empty bytes only for that marker;
missing observations still fail. This replaces no
compiler return-shape check. Helpers with storage writes are rejected because
the importer does not yet validate solc's nested expression evaluation order.
Constructor execution and state-variable initialization remain outside the
runtime-slice claim.

Scalar mappings reuse the model's mapping-to-struct representation with one
internal member at word zero. The importer trusts solc's mapping key types and
value widths, checks the reported byte size, and preserves upper bits on narrow
writes. Boolean values occupy one byte and reads normalize nonzero to true.
This representation is an importer lowering, not a proof of solc equivalence.
The mapping sequence and its three variants provide sampled real A/B/C evidence.
Their Denote route uses the actual Keccak oracle. Slot instrumentation evaluates
keys in the current state and records the nested hash plus member offset; this
instrumentation remains part of the differential harness trust boundary.

Storage access tracing now follows only the selected conditional branch and
advances branch-local state through the actual executor, stopping at return or
revert. Pure arithmetic/bitmask operands are recursively inventoried. Unsupported
expressions still fail observation; no accesses are inferred from execution
success. The original full-outcome trace agreement theorem is unchanged.

The typed accessors that the import also generates (`example.f`,
`example.position.credit`, ...) add no trust: they are Lean definitions over
the model, through `runFunction` and `readMember` in
`Compiler/SolidityImport/Access.lean`. A theorem stated with them is
kernel-checked against those definitions. They inherit the model's layout, so
they mean the Solidity storage member only as far as the imported layout does.

The source digest hashes `Import.lean`, `Coverage.lean`, `Report.lean`,
`Quote.lean`, and `Profile.lean` from
the package that contains them: the Verity tree itself, or
`.lake/packages/verity` when a downstream package elaborates the import. The
pinned solc binary stays in the elaborating package's
`.lake/solidity-import/solc-0.8.34`.

The frontend is in the trust base. A covered model is not a proof that the
model matches the Solidity source or solc's bytecode. `storageLayout` slots and
packed offsets are copied from pinned solc 0.8.34
(`0.8.34+commit.80d5c536`; linux-amd64 and macosx-amd64 SHA-256 pins in
`Import.lean`). `mappingSlot` in the denotation oracle is not Keccak. Numeric
claims are about the values `structMember` reads back.

Checked `uint256` and narrower unsigned arithmetic is lowered to `Stmt.ite` plus
`Stmt.panic`, not to a second interpreter. Explicit `uint128(x)` is truncation
(`bitAnd` with `2^128-1`). Ternaries are `Stmt.ite`, so the untaken branch is
not evaluated. Library helpers in an accepted acyclic slice are inlined.
`UtilsLib`-style `min` is the Yul term `xor`/`mul`/`lt`, not a renamed `Expr.min`.
Generated scalar bindings are hygienic, and helper-local bindings are scoped.
Only reached storage fields are decoded. Namespace-qualified output names and
framed-JSON provenance are deterministic. Implicit root returns, named call
arguments, virtual dispatch, and unsupported signed operations are rejected.
The slice makes no dynamic ABI-head claim: that unrelated denotation extension
is not part of this change. Solidity sources are Lake inputs only when the
consumer declares them (`input_dir` + `needs`); consumers should also
re-elaborate in CI to verify freshness against a compiled import.

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

The repository currently has 0 `sorry` placeholders across the `Compiler/**/*.lean` and `Verity/**/*.lean` proof modules that participate in the verified compiler stack. Layer 2 (Source → IR) and Layer 3 (IR → Yul) proof scripts are fully discharged, and it now has 1 documented Lean axiom (`solidityMappingSlot_injective`). See [AXIOMS.md](AXIOMS.md) for details. Generated trust-boundary artifacts live in `artifacts/`.

## What's Verified

- **Layer 1**: A generic typed-IR compilation-correctness core exists, but the active contract-level bridges are still instantiated per contract and internal-helper proof reuse is not yet a first-class generic interface.
  This names the frontend EDSL-to-`CompilationModel` bridge only; the
  contract-specific specification theorems in `Contracts/<Name>/Proofs/` are a
  separate proof layer about human-readable contract behavior.
- **Layer 2**: A generic whole-contract theorem is proved for the current supported `CompilationModel` fragment. `supported_function_correct` is now a real theorem, the initial-state normalization step is proved, the former generic body-simulation axiom has been eliminated, and the theorem surface makes explicit that the observed transaction-context fields must already be normalized to the bounded source-side `Address`/`Uint256` domains. Remaining Layer 2 work is now about widening the supported fragment and helper-aware completeness, not repairing `sorry` placeholders.
- **Layer 3**: IR → Yul preservation is generic at the proof surface, and the remaining dispatch bridge now lives as an explicit theorem hypothesis rather than a Lean axiom. The checked contract-level theorem surface makes the dispatch-guard safety preconditions explicit: non-payable cases must see word-level zero `msg.value`, and each selected function case must have a non-wrapping calldata-width guard.

Current theorem totals, property-test coverage, and proof status live in [docs/VERIFICATION_STATUS.md](VERIFICATION_STATUS.md).

## Trusted Components

### 1. Solidity Compiler (`solc`)
- **Role**: Compiles Yul → EVM bytecode.
- **Version**: 0.8.33+commit.64118f21 (pinned).
- **Mitigation**: CI enforces pin and Yul compileability checks.

### 2. Lean Axioms
- **Role**: Bridge remaining proof obligations not yet fully discharged.
- **Status**: 1 documented axiom in [AXIOMS.md](AXIOMS.md): `solidityMappingSlot_injective` (collision-resistance of `keccak256(abi.encode(key, base))`, not keccak injectivity on all inputs). The mapping-slot *range* axiom has been eliminated via the kernel-computable Keccak engine. Selector computation is kernel-computable, the Layer 2 generic body-simulation axiom has been eliminated, and the Layer 3 dispatch bridge remains an explicit theorem hypothesis rather than a Lean axiom.
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
- **Fork dependency**: Verity pins [`lfglabs-dev/EVMYulLean`](https://github.com/lfglabs-dev/EVMYulLean), a fork of [`NethermindEth/EVMYulLean`](https://github.com/NethermindEth/EVMYulLean). The pinned commit is recorded in `lake-manifest.json` under the `evmyul` package. The exact divergence from upstream is enumerated in [`artifacts/evmyullean_fork_audit.json`](../artifacts/evmyullean_fork_audit.json), regenerated by `scripts/generate_evmyullean_fork_audit.py` and validated by `make check`. As of the current pin, the fork is 18 commits ahead of `upstream/main` and 0 behind: the audited changes are non-semantic visibility, FFI-body-exposure, and Lean 4.22/4.24/4.31 toolchain-compatibility changes; none changes EVM/Yul execution semantics, so upstream Ethereum conformance test coverage continues to apply transitively. In addition to the `make check` validation, a weekly scheduled GitHub Actions workflow ([`.github/workflows/evmyullean-fork-conformance.yml`](../.github/workflows/evmyullean-fork-conformance.yml)) runs `make test-evmyullean-fork`, which re-verifies the fork audit artifact against `lake-manifest.json`, checks the EVMYulLean native lowering report, rebuilds the native transition harness, rebuilds the public EndToEnd EVMYulLean target, and rebuilds the native builtin routing lemmas together with the native bridge smoke tests and 0 concrete bridge tests, surfacing any upstream drift as a red workflow plus an automatically opened or updated GitHub issue for scheduled/manual failures.
- **Remaining gap for whole-program retargeting**: The public EndToEnd native surface is in place, but the per-`BridgedStraightStmt` IR↔native observation-equivalence framework that would land truly unconditional S1–S8 / F2/F4/F6/F7 / true S8 has not been built yet — that work is multi-week and tracked separately. The external-call/function-table family now has function-table-aware closure scaffolding in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanCallClosure.lean` (per-family source-level predicates, per-family `compileStmt`/`compileStmtList` closure theorems, `ECMBridgeable` per-module obligation, and a `BridgedStmts`-preserving `pfx ++ sfx` composition lemma); end-to-end wiring through `SupportedFragment`/`SupportedSpec` for whole contracts using these constructors is the next milestone.
- **Implication**: Semantic correctness does not imply gas-safety.
- **Proxy note**: `delegatecall`-based proxy / upgradeability flows still sit outside the current native verified runtime model. Archive `--trust-report` and use `--deny-proxy-upgradeability` when proxy semantics must remain outside the selected verified subset (issue `#1420`).

### 6b. Modeled-callee `linked_contracts` bindings

- **Role**: A `linked_contracts name : IFace := Callee` section tells the
  model plane that an interface-typed value is the named `verity_contract`.
- **Trust**: model-level assumption that the runtime address holds that
  contract. There is **no bytecode claim**: compilation-model lowering of a
  bound call is the same ABI/ECM call as an unbound interface call.
- **Semantics**: hops in `Verity.MultiContract.MultiWorld` (`ModeledCall.lean`).
  The executable plane of a bound call is `Contract.hopCall` /
  `Contract.hopCallView`: every word-valued storage channel is namespaced
  per contract across a distinct-address hop — scalar slots move through
  `StorageKey.contractSlot`, and address slots, transient slots and all
  mappings (`addr` / `transient` / `map` / `mapUint` / `map2`) through
  `StorageKey.scoped` (G24, #2440; `ContractState.switchSlotWorld`,
  `enterHop_readAddrSlot` / `enterHop_readMap` / …,
  `exitHop_enterHop_storageWords_plain`). A callee never sees or clobbers the
  caller's same-numbered address slot or mapping entry. Success commits the
  callee world, revert restores the pre-call snapshot, and view hops discard
  callee writes. Unbound interfaces still use the adversary-oracle stub.
  **Remaining boundary**: `storageArray` (dynamic-array storage, a separate
  `ContractState` field) is *not* namespaced and stays global across hops,
  so a cross-contract statement that reads a dynamic array inside a hop is
  not sound in this plane.
  Named-callee bindings cannot be cyclic (the callee must be declared
  first); cyclic pairs use `deferred` bindings (below). `callEntry` is
  unchanged (still rejects `caller = callee`); self-calls use the isolated
  CALL-shaped `selfCallEntry` / `Contract.selfCall`.
- **Public getters (G23, #2439)**: a bound typed call whose method names a
  public storage field of the callee (Solidity auto-generated getter) lowers
  to `Contract.hopCallView target (<typed read of that field>)`:
  `getStorage` (Uint256; a `Bool` interface return decodes the 0/1 word as
  `word != 0`, the same decoding `ExternalResult Bool` applies to an ABI
  word), `getStorageAddr`, `getMapping`, `getMappingUint`, `getMapping2`.
  Packed, transient, and other field shapes are rejected at elaboration.
  The compilation-model lowering is unchanged (ABI getter call).
- **Deferred bindings (G15, #2415)**: `linked_contracts name : IFace :=
  deferred` binds an interface to a contract declared later (cyclic
  pairs). No callee body is linked: executable typed calls keep the ABI
  external-call lowering (`external*CallContractWordsTo` / effect variants)
  but always consume the threaded `ExecutableCallContext` (the enclosing
  function, and every helper that transitively calls it, takes the context
  binder like a reentrancy-window function; it never falls back to the fixed
  stub). **Trust boundary**: a deferred call is only as faithful as the
  responder the proof instantiates the context with. With
  `ExecutableCallContext.stub` it returns the fixed stub word (unchanged
  behaviour). The faithful responder is
  `AdversaryModel.withViewLinks` / `ExecutableCallContext.withViewLinks`,
  which answers selected static sites (keyed by interface method name and
  target address) by running a linked Verity body in `Contract.hopCallView`;
  `Contracts.externalStaticCallContractWordsTo_withViewLinks` proves the call
  then returns exactly the decoded hop words and leaves caller storage
  unchanged. Mutable deferred calls have no faithful responder combinator
  yet (they are answered by the instantiated adversary). Compilation-model
  lowering is unchanged.
- **Context forwarding into bound callees (G26)**: a bound hop into a callee
  function that takes the `ExecutableCallContext` (it reaches a `deferred`
  link or opens a reentrancy window) forwards the caller's context. The
  caller itself then takes the context binder (same propagation as deferred
  calls, through the helper fixed point), so the callee's nested calls are
  never answered by the fixed stub merely because the caller had no external
  call of its own. Bound hops into context-free callees and storage-field
  getters keep the context-free signature.
- **Mutable typed tuple calls (G14 residual)**: `let (a, b) ← s.m x` on a
  state-changing interface method (static single-word returns). Bound
  (named): `Contract.hopCall target (Callee.m x)` (callee revert bubbles);
  unbound / deferred: the mutable ABI external call with arity = number of
  results, answered by the threaded context. Compilation model:
  `Compiler.Modules.Calls.withReturnsModule` (ABI `call`, requires
  `returndatasize >= 32 * n`, binds word `i` to result `i`; trust surface
  `abiBoundary`, assumption `external_call_abi_interface`). View tuple calls
  keep the static oracle-summary ECM.
- **Author rule — one interface, several runtime contracts (G25)**: a named
  binding dispatches by interface (and receiver/parameter name), **not** by
  the runtime target address. If one interface is called on addresses that
  hold different contracts, a named binding runs the bound callee's body for
  every target, which is unfaithful for the other targets. Use `deferred` for
  such interfaces and instantiate the context with `withViewLinks` keyed by
  target address (`links "IFace.method" target`).

### 7. External Call Modules (ECMs)
- **Role**: Reusable typed external call patterns (ERC-20 writes/reads including `totalSupply`, ERC-4626 preview/conversion helpers plus `totalAssets`, `asset`, `max*` limit reads, and `deposit`, oracle reads, precompiles 0x01 / 0x02 / 0x06 / 0x07 / 0x08 — `ecrecover`, `sha256`, BN254 `bn256Add`, `bn256ScalarMul`, `bn256Pairing` — callbacks, and same-contract `selfDelegateMulticallBytes`).
- **Trust**: Each module's `compile` produces correct Yul. Bug in one module doesn't affect others. `selfDelegateMulticallBytes` is an explicitly trusted ECM boundary under `self_delegate_multicall_bytes_revert_bubbling`: the compiler emits concrete bounds checks for ABI element offsets, including a pre-add overflow guard before forming the calldata head offset, but full non-empty multicall revert-bubbling semantics are not yet machine-proven. First-class self-delegate sequences (`Verity.MultiContract.denoteSelfDelegateCalls`) are ordinary Lean functions: success threads one world, failure/revert restores the sequence-entry world and records returndata; they do not discharge the ECM assumption. `solidityMappingSlot_injective` remains the one documented Lean axiom.
- **Mitigation**: Axiom aggregation at compile time (`--verbose`), machine-readable trust-surface emission via `--trust-report <path>`, and a fail-closed verification gate via `--deny-unchecked-dependencies` when unchecked foreign surfaces must be excluded. See [docs/EXTERNAL_CALL_MODULES.md](EXTERNAL_CALL_MODULES.md).
- **Summary conformance bridge**: `Verity.Core.Model.SummaryBridge` defines `Conforms`, connecting `StatefulExternal.Summary` (the typed ECM interface contract) to the executable `AdversaryModel` boundary: caller proofs may quantify over summary-conforming adversaries, in which case each summary's `pre`/`post`/`revert` relations and its declared mutability become *proof obligations on the modeled adversary*, not axioms. The staticcall no-external-mutation law is derived from conformance. An adversary's `failure` response carries no summary obligation (opaque exceptional failure; never committed). Whether a given real callee satisfies its summary remains the per-summary trust assumption listed via `assumptionNames`.
- **Caller-frame preservation**: The EVM frame condition (external `CALL` cannot mutate caller storage / transient storage / memory outside the declared output buffer) is now a *theorem* of `Verity.EVM.Frame` rather than an assumption. Downstream proofs consume `external_call_preserves_caller_storage` etc. directly. The abstract memory model used by these theorems is `Verity.EVM.MemoryModel`; the solc memory-layout schema and call-buffer-disjoint-from-heap result are in `Verity.EVM.Layout`. EvmYul ↔ abstract-model correspondence remains the open follow-up.

### 8. Lean Kernel
- **Role**: Proof checker soundness. Foundational assumption for all Lean-based verification.
- **Native decision proofs**: `native_decide` relies on native code generation.
  Lean 4.31 may expose that boundary in `#print axioms` as a generated per-proof
  constant named `…._native.native_decide.ax_<digits>` instead of
  `Lean.ofReduceBool`. The audit accepts only that narrowly shaped family and
  records both forms under the native compiler (`Lean.trustCompiler`) boundary,
  not as Verity project axioms.
- **Lean 4.31 kernel string facts**: The closed scratch-name facts
  `Compiler.CompilationModel.compatScratch_startsWith_reserved` and
  `Compiler.CompilationModel.compatScratch_not_internalImmutable` are proved
  with Lean 4.31's public `String.startsWith_string_iff` and
  `String.startsWith_string_eq_false_iff` lemmas followed by kernel `decide`.
  They remain grouped in
  `Compiler/CompilationModel/ReservedScratchNames.lean`, and no longer add
  `Lean.ofReduceBool` or `Lean.trustCompiler` to the trust surface.

### 9. Macro Elaborator (`verity_contract`)
- **Role**: Generates both EDSL `Contract` monad value and `CompilationModel` from one syntax tree.
- **Status**: Trusted unverified metaprogram ([Verity/Macro/Translate.lean](../Verity/Macro/Translate.lean)).
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
  metadata, and local obligations. The bridge emits comment-only provenance
  markers around each fragment; checked-arithmetic optimization treats those
  marked regions as opaque and copies them unchanged. Raw memory reverts use
  `UnsafeYulFragment.rawRevert` through `Stmt.unsafeYul`.
- **Mitigation**: Keep common typed primitives such as `mstore` and
  `calldatacopy` first-class only when Verity has stable semantics and they are
  useful for proofs. Treat other raw Yul as an explicit trust-report surface,
  and use `--deny-local-obligations` / low-level deny gates for strict builds.
- **Reference**: See [docs/LOW_LEVEL_YUL.md](LOW_LEVEL_YUL.md).

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
- **Reference**: See [docs/INTRINSICS.md](INTRINSICS.md).

## Semantic Caveats

### Wrapping Arithmetic
`Uint256` arithmetic is **wrapping modulo 2^256**, matching the EVM. This is
proven, not assumed (see `Compiler/Proofs/ArithmeticProfile.lean`). Checked
operations (`safeAdd`, `safeSub`, `safeMul`, `safeDiv`) are available for
explicit overflow and division-by-zero protection.

The unsigned Solidity-0.8-style `addPanic`/`subPanic`/`mulPanic`/`divPanic` bind forms
use the closed `PanicCode` domain: the macro emits a matching failure predicate
plus `Stmt.panic .arithmeticOverflow` or `Stmt.panic .divisionByZero`, which
compiles to the canonical 36-byte `Panic(uint256)` ABI payload (selector
`0x4e487b71`, followed by code `0x11` or `0x12`). Direct Lean helper execution
retains compatibility diagnostic strings; macro-generated compilation bypasses
that path and does not encode those strings as `Error(string)`.
`Compiler.Proofs.IRGeneration.PanicPayloadIR` proves the abstract memory writes
and revert result for every in-range code and both typed constructors; its
interpreter does not observe returned bytes. Separately,
`Compiler.Proofs.YulGeneration.PanicPayloadBytes` proves the exact 36-byte
payload for the emitted panic AST, using EVMYulLean's byte-addressed `mstore`
and `evmRevert` operations for arbitrary initial memory. This local fragment
retains the bytes that the native Yul revert exception discards; it is not a
proof of full native Yul execution or solc-generated bytecode. These proofs are
kernel-checked and introduce no new axiom or native-code reduction dependency.
General runtime panics and enum guards such as `0x21` remain on
the raw `Stmt.panicCode Expr` path; raw lookalikes are not optimizer evidence.

This does not widen the current generic whole-contract proof fragment:
typed and raw panic statements remain excluded by its typed-revert
effect-surface gate. Separately, the post-codegen `CodegenCommon` peephole that
replaces the exact pair of adjacent statements—a guarded typed panic followed
by its arithmetic result binding, together forming the guard/panic/arithmetic
sequence—with the corresponding checked helper call is not covered by an
end-to-end preservation theorem. Its present assurance is fail-closed
structural matching plus positive and negative feature tests.
The `compiler-regressions` CI job explicitly builds `Compiler.PanicCodeRegressionTest`,
and the workflow sync specification requires that step. CI enforcement does not
replace the missing optimizer-preservation theorem.
All four rewrites require numeric-literal or variable-reference operands;
calls and compound expressions are excluded to preserve operand evaluations.
ECM regions are inspected automatically, without an author opt-in. Each emitted
deployment/runtime section independently requires exactly one canonical definition
of all four arithmetic and both panic helpers and no conflicting bindings, including
nested locals, parameters, returns, and functions. ECM does not itself insert
helpers. Explicit unsafe-Yul regions stay opaque, matches cannot cross region
markers, and malformed regions disable the pass. Reserved ECM marker text in
module output forces opacity. The ECM wrapper lemma preserves bridge syntactic
support, not execution semantics; these checks introduce no new proof claim.
This is an existing compiler-validation boundary whose behavior changed with
the structured-panic migration; it introduces no new Lean axiom. See
[docs/ARITHMETIC_PROFILE.md](ARITHMETIC_PROFILE.md).

### Revert-State Modeling
High-level semantics can expose intermediate state in reverted computations. EVM reverts discard state. Contracts should use checks-before-effects. See [REVERT_STATE_MODEL.md](REVERT_STATE_MODEL.md).

### Top-Level Transaction Rollback (`denoteTransaction`)
`Verity.Core.Model.CallProgramRollback.denoteTransaction` restores the pre-transaction caller world on a top-level `.revert` *by construction*: the `denoteTransaction_revert_*` theorems characterize this wrapper's behavior, they do not derive rollback from lower-level EVM semantics. That the EVM's actual transaction-revert behavior matches this model (full world restoration, gas remains charged, returndata exposed) is a trusted modeling assumption, on par with §6 (EVM/Yul Semantics).

### External-Call Gas Discipline (short-term model)
`Verity.Core.Model.GasCoupling` ties the modeled callee cost to the call's gas allowance: a `GasFaithful` adversary can only succeed within the allowance, must fail (never commit) when over budget, and cannot claim more gas than forwarded. Failure causes (`outOfGas` vs. opaque exceptional halt) are modeling artifacts: `denoteCall_congr`/`denote_congr` prove observations are determined by the adversary's responses alone, so causes cannot leak to the caller — matching the EVM's zero-success-bit observability. The caller-has-enough-gas-for-its-handler assumption is the explicit `CallerCoversAllowance` hypothesis. Opcode-level gas accounting (EIP-150, warm/cold, refunds, stipend) is out of scope for this model and remains a dedicated roadmap lane.

### Event Emission (preserved observable, scalar fragment)
Final-result event preservation — `encodeEvents source.events = ir.events` in
the transaction's observable result, not merely an intermediate state — is
**proven** for the scalar fragment by
`Compiler.Proofs.IRGeneration.Contract.compile_preserves_semantics_with_scalar_events`
and, for the guarded (`nonreentrant`-aware) pipeline, by
`Compiler.Proofs.IRGeneration.compile_preserves_semantics_guarded_with_scalar_events`
(`Compiler/Proofs/IRGeneration/GuardedScalarEvents.lean`; on the scalar
fragment every supported function is lock-free, so the guarded source
semantics provably collapses to the plain one). Outside the proven fragment:
- `Stmt.rawLog` emission is not modeled — this is what the machine-readable
  trust-report slice `notModeledEventEmission` and the `--deny-event-emission`
  gate flag.
- Declared `Stmt.emit` outside the scalar fragment (nested under
  `ite`/`forEach`, non-scalar or more than 3 indexed params, non-atomic
  args, or inside a function that carries a `nonreentrant` lock) is
  excluded by the support witness (`SupportedBodyInterfaceWithScalarEvents`)
  rather than reported in `notModeledEventEmission`: the boundary is
  machine-checked at the theorem surface, but the trust-report slice does
  **not** enumerate it — the slice only ever names `rawLog`.

### Canonical `StorageKey` backing (`ContractState.storageWords`)
Word-valued source storage is one map `StorageKey → Uint256`. The key is
an injective inductive (`slot` / `contractSlot` / `transient` / `addr` /
`map` / `mapUint` / `map2` / `scoped`); public accessors keep the old channel
names. `scoped c k` is contract `c`'s parked copy of a non-slot key `k` across
hops; it has no flat compiler-channel counterpart (`storageKeySlot` maps it to
`none`).
This is a representation change, not a new trust boundary: lens laws use
constructor injectivity. Solidity keccak slot derivation lives in
`Compiler.Proofs.Storage.MappingCoherence.storageKeySlot`. Address-,
uint-, and nested-address shadow-vs-flat agreement
(`MappingCoherent` / `MappingCoherentUint` / `MappingCoherentMap2`) is
defined there and proved for `defaultState` and for an aligned
`writeMap*`+`writeSlot` pair; other pairs require an explicit
non-alias hypothesis. A CompilationModel field list collapses to those
keys via `FieldStorageKey` (root plus typed `map`/`mapUint`/`map2`
entries). Address-keyed `mappingStruct` / `mappingStruct2` members
collapse to `mappingSlotLocation` / `nestedMappingSlotLocation`
(base mapping slot plus `wordOffset`). Compatibility `aliasSlots`
are extra compiler write targets; only the resolved head has a
`StorageKey`. bytes32-keyed maps collapse to `solidityMappingSlot`
of the 32-byte word; there is no `StorageKey.mapBytes32`. Mixed
All nine `MappingType.nested` key-type pairs collapse to
`abstractNestedMappingSlot`.
Packed subfields extract from the same `storageKeySlot` word; they
are not a different slot. For `width < 256` that extract is the
`compiledPackedRead` of the storage word. A named mapping field's
derived `storageKeySlot` is the flat slot `MappingCoherent*`
compares against, including a finite listed pair
(`MappingCoherentOn`). An unoccupied keccak-derived mapping slot
encodes as that shadow via `encodeStorageAt`. A lone flat
`writeSlot` keeps a listed pair coherent when the written word
is distinct from that pair's derived slot. A lone
`writeTransient` keeps every listed pair coherent because
transient keys are a different `StorageKey` constructor. `encodeStorageAt` at a persistent unpacked uint256 or address field
is the corresponding lens once `firstFieldWriteSlotConflict` is
none; `findResolvedFieldAtSlot` is derived, not hypothesized.
A finite list of address-, uint-, or nested-address pairs
stays coherent under an aligned write when the list carries an
explicit pairwise derived-slot certificate (`MappingCoherentOn` /
`MappingCoherentUintOn` / `MappingCoherentMap2On`); that is not a
global (all-keys) claim. Cross-channel preservation of another
list likewise takes an explicit derived-slot inequality. C5 step 4
is complete under `solidityMappingSlot_injective`: global aligned
`writeMap*`+`writeSlot` preserves `MappingCoherent*`;
`writeTransient` preserves them by constructor injectivity; a lone
`writeSlot` needs an image-avoidance `∀`. That `∀` is discharged
for `writeAddrSlot` and `writeArray` (they never write
`StorageKey.slot`). Keccak injectivity on
arbitrary byte strings is **not** assumed.
The all-keys (`∀ StorageKey`) form of that claim is
`Compiler.Proofs.Storage.MappingCoherentGlobal.MappingCoherentAllKeys`,
stated against the field-list collapse
`storageKeySlot : List Field → StorageKey → Option (Channel × Nat)`
(`Channel` = `persistent` / `address` / `transient` / `contract c`; the
model does not identify `contractSlot 0` with `slot`). The declared
layout is load-bearing, not decoration: a mapping key collapses only
when the resolved field at its base slot declares the matching
`MappingType`, so two mapping channels cannot share a base slot and
`solidityMappingSlot_injective` separates their derived images.
Aligned `writeMap` / `writeMapUint` / `writeMap2` + `writeSlot`,
`writeAddrSlot`, and `writeTransient` preserve it; a lone `writeSlot`
takes the same image-avoidance `∀` (`DerivedMappingSlotsAvoid`). The
simple-vs-nested cross case additionally takes an explicit per-contract
layout certificate `MappingBasesNotDerived` (a declared mapping base
slot is not itself keccak-derived) — a hypothesis discharged per
contract, not an axiom. Under that invariant the lens read equals the
flat `encodeStorageAt` read at the derived slot
(`readMap_eq_encodeStorageAt_of_coherent` and the `mapUint` / `map2`
variants), reusing the same non-occupation hypotheses `FieldEncode`
already takes.

**Known divergence — dynamic-array element slots (`unsupported`).**
The source model and the Yul model derive dynamic-array element
addresses differently and are **not** reconciled here.
`Compiler/Proofs/IRGeneration/SourceSemantics.lean:330-350`
(`findDynamicArrayElementAtSlot`) places element `i` of the array
rooted at slot `s` at `solidityMappingSlot s i` =
`keccak256(abi.encode(i, s))`, a 64-byte mapping preimage.
`Compiler/Proofs/Storage/StructArrayStorage.lean:666-671`
(`storageArrayBasePointer` / `storageArrayElementPointer`) uses the
real Solidity layout `keccak256(bytes32(s)) + i`, a 32-byte preimage
plus an arithmetic offset. Missing feature, precisely: *the source
semantics has no array-element slot derivation of the form
`keccak256(bytes32(slot)) + index`* — it reuses the mapping
derivation. No shim asserts the two equal. Containment:
`storageKeySlot` returns `none` at a persistent root whose resolved
field is a `dynamicArray`
(`storageKeySlot_slot_dynamicArray`), so `MappingCoherentAllKeys`
claims nothing about dynamic-array roots; `encodeStorageAt` reads a
list length there, not a word.
`storageArray` and `knownAddresses` are still separate fields;
word-channel / array-channel independence is proved in
`Compiler.Proofs.Storage.SeparateChannels`.

### External-Call Journal (`ContractState.calls`)
`ContractState.calls` is an append-only journal of observed external calls
(`Verity.ExternalCall`: site id, kind, target, value, calldata, control,
returndata). It is a **proof-side observable, not EVM state**: the EVM keeps
no such record, so nothing about it is claimed by semantic preservation.
Two deliberate modeling choices in
`Verity.Core.Model.DenoteExternalCalls.denoteCallJournaled` and the source
primitive `externalCall` (`Verity.Core.Model.ContractExternalCall`):
1. **The journal survives caller-side rollback.** A failed or reverted call
   restores the caller world *except* `calls` — otherwise reverted calls
   would be unobservable and per-iteration reasoning over retrying loops
   would be impossible. Consequently `externalCall` never raises a monadic
   revert; the callee's outcome is reported in-band via
   `ExternalCallResult.control` (a full monadic revert through
   `Contract.run` still discards the journal with the rest of the snapshot,
   matching EVM top-level semantics — `externalCallRequireSuccess` opts into
   that deliberately).
2. **The adversary cannot write the journal.** Even a committed
   `call`/`delegatecall` transition has its `calls` field overwritten with
   `pre.calls ++ [entry]`: the journal is the caller's observation record,
   not adversary-controlled state.
`denoteCall` itself is unchanged; all previously proven world/gas laws hold
verbatim.

The **EDSL executable plane** journals through the same field: the linked-call
primitives (`Contracts.externalCallBind`, `Contracts.callResultWords`,
`Contracts.tryExternalCallWords`, the `safeTransfer` family) append one entry
per call. General linked calls are name-keyed (`Contracts.linkedCallEntry`,
`siteId`/`target` = 0). ERC-20 writes record the token as `target`, their actual
wrapper arguments as `calldata`, and the wrapper name. `ExternalArg.toWords`
retains scalar values and length-prefixes arrays/byte arrays before their full
recursive content; this is a deterministic journal-word encoding, not a claim
of byte-for-byte EVM ABI layout. Trust boundaries of that plane:
- **Return values are deterministic stubs, not adversary models.** In-band
  words come from `externalCallStubWord`; the success bit is
  `externalCallStubSuccess` (`false` only for the reserved callee name
  `"fail"`). Supported single-word results decode that same word; aggregate
  and no-result stubs use their inhabited default. Executable-plane theorems
  about call *outcomes* are therefore claims about the stub, not about a real
  callee; adversarial reasoning lives in the model plane (`DenoteExternalCalls`).
- **`externalCallWords` (pure expression form) does not journal.** It is not
  monadic, so `externalCall name [args]` used as a pure expression remains
  observationally silent; only the monadic forms journal. Specs that need
  call observability must use the monadic primitives.
- **`callExternal name(args)` surface** remains an unmodeled no-op at this
  plane.
- **Hashed mapping accessors are executable, on the `.slot` channel.**
  `getMappingN`/`setMappingN`, `getMappingWord`/`setMappingWord` and the
  generated `structMember`/`setStructMember` family read and write
  `ContractState.storage` at the Solidity keccak slot
  (`Compiler.Proofs.abstractMappingSlot`, folded left over the key path, plus
  the member word offset modulo `2^256`); `transient` mapping chains use the
  `.transient` channel. `structMembers`/`structMembers2` destructuring lowers
  to those reads. This channel is disjoint from the constructor-keyed
  `storageMap`/`storageMapUint`/`storageMap2` channels behind
  `getMapping`/`getMappingUint`/`getMapping2`; a field is accessed through
  exactly one family, fixed by its declared storage type. Distinctness of two
  hashed slots with different keys rests on the existing
  `solidityMappingSlot_injective` axiom; adjacent struct words are distinct
  without it (`Contracts.structSlot_ne_succ`). The pure expression form
  `structMembers` outside `let (..) :=` / `return` still yields `default`.
- **`externalCallBindTo` journals target and value and debits ETH
  on success.** It is still a stub for the callee return word
  (`externalCallStubWord`). Real callee state is the model-plane
  `AdversaryModel` / `Verity.MultiContract` hop, not this stub.
- **Base `FunctionSpec` denotation (`Denote.evalExpr` /
  `execStmt`) still treats raw `Expr.call` and
  `Stmt.externalCallBind` as outside the SourceSemantics-agreeing
  fragment.** The widened fragment is
  `DenoteFunctionCalls.denoteFunctionWithCalls`.
- **Base `withTransactionContext` still does not credit
  `selfBalance`.** Payable FunctionSpec denotation uses
  `withPayableCallContext`. Multi-contract hops use
  `MultiContract.withCallContext`. A call that uses neither still
  has a stale balance.
- **`MultiContract` Bus → Gateway → Vault → (Lido | request) is a
  model ensemble**, not a compiled protocol and not an L2
  preservation claim. The generic `CallFrame` / `executeCall` boundary now
  obtains control, returndata, the committed callee post-state, and the caller
  journal from one `CalleeExecution`; failed/reverted executions restore the
  caller/callee snapshots apart from the caller observation. The first
  official adapter executes a source-shaped `FunctionSpec` through
  `DenoteFunctionCalls.callFunction`; unlike the lower-level executor callback,
  that entrypoint does not accept injected control, returndata, or post-state.
  This boundary currently rejects
  `staticcall`, `delegatecall`, self-calls, and target/address mismatches;
  admitting those requires their distinct frame invariants rather than
  pretending ordinary-call semantics apply.
- A full monadic revert through `Contract.run` rolls the journal back with
  the rest of the snapshot (top-level EVM semantics), unlike the model
  plane's caller-side rollback survival described above.

### Reentrancy Guard (`nonreentrant(lockField)`)
Functions annotated `nonreentrant(lockField)` are compiled with a
**transient-storage** reentrancy guard prologue (#1893): an
`if eq(tload(lockSlot), 1) { revert(0, 0) }; tstore(lockSlot, 1)` pair runs
before any user-authored Yul. Transient storage (EIP-1153, Cancun+) auto-clears
at end-of-transaction, so the guard does not need an explicit release path —
early `return`, `revert`, or panic cannot leak the lock across transactions.
The guard exempts the function from CEI ordering enforcement, so state writes
after external calls are permitted within reentrancy-protected entry points.

`Verity.Core.Model.NonReentrantGuard.guarded` now gives this transformation a
*proved source semantics*: lock free ⇒ the body runs with the lock observably
set and successful exits release it; lock held ⇒ revert with the pre-call
state unchanged; and whole reentry schedules of same-lock guarded entrypoints
collapse to the identity on locked states (`runSeq_guarded_locked_id`) — the
reentry window is closed at the model level. On the compiled side,
`Compiler.Proofs.IRGeneration.NonReentrantGuardIR` proves the emitted
prologue/release statements under the IR interpreter: locked entry reverts
untouched, free entry acquires the lock and changes nothing else, the spliced
release resets it (acquire/release round-trips the transient store), and the
Yul decision `eq(lock,1)` agrees with the model's `lock ≠ 0` on reachable
binary lock values. `Compiler.Proofs.IRGeneration.SpliceSimulation` now proves the full guarded
unit end to end for the loop/switch-free fragment with compiler-emitted
exits: the general splice simulation (`execIRStmts_spliced`), both
`applyLockReleaseOnExits` branches, and
`execIRStmts_guardedUnit_fallthrough`/`_halting` — the compiled
prologue + release-wrapped body mirrors `guarded` exactly (locked entry
reverts untouched; free entry runs from the acquired state with successful
outcomes released). Still trusted: `switch` bodies and loops in guarded
functions, `selfdestruct` in guarded bodies (excluded from the simulation fragment: the
splice inserts no release before it, and a self-destructed contract's lock is
moot — `invalid` is now modeled as a frame halt and covered by `ModeledHalt`),
and the `compile_preserves_semantics`
threading that would lift the supported-fragment `noNonReentrant`
restriction.
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
- **Reference**: [Verity/Core/Reentrancy.lean](../Verity/Core/Reentrancy.lean),
  [Contracts/ReentrancyRelyGuarantee/Contract.lean](../Contracts/ReentrancyRelyGuarantee/Contract.lean).

### Cross-Function Reentrancy Gate (fail-closed)
Every function whose body opens a reentrancy window (`externalCallBind`,
`tryExternalCallBind`, a state-changing `call`-summarised `ecm`, a non-builtin
`externalCall` expression, or an `unsafeYul` fragment carrying an external-call
mechanic) and that is **not** `view`/`pure` must declare a reentrancy
disposition or compilation fails (`validateReentrancyDisposition`, keyed on
`stmtOpensReentrancyWindow`, in
[Compiler/CompilationModel/Validation.lean](../Compiler/CompilationModel/Validation.lean)).
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
[Verity/Macro/Internal.lean](../Verity/Macro/Internal.lean)), because routing it
through the lock-free shadow would run the guarded body without the lock and
silently bypass the only reentrancy protection it had. Calling a function that
*also* carries `reentrancy_trusted` is accepted — that disposition is a global
author assertion covering every entry path, including the lock-free internal one.
This mirrors the parse-time rejection of an `internal nonreentrant(<lock>)`
helper (`NonreentrantInternalHelperRejected`, #1971).

- **Reference**: [Compiler/CompilationModel/Validation.lean](../Compiler/CompilationModel/Validation.lean)
  (`validateReentrancyDisposition`, the cross-function reentrancy gate — a
  dedicated pass run after call well-formedness, distinct from the
  single-function CEI check in `validateFunctionSpec`);
  [Verity/Macro/Internal.lean](../Verity/Macro/Internal.lean)
  (`ensureCallableAsInternalHelper`, the lowering-time rejection of internal
  calls to lock-only `nonreentrant` entries).
- **Regression evidence**: [Contracts/Smoke/SecurityCombos.lean](../Contracts/Smoke/SecurityCombos.lean)
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

- [AXIOMS.md](AXIOMS.md) | [INTRINSICS.md](INTRINSICS.md) | [ARITHMETIC_PROFILE.md](ARITHMETIC_PROFILE.md) | [REVERT_STATE_MODEL.md](REVERT_STATE_MODEL.md)
- [EXTERNAL_CALL_MODULES.md](EXTERNAL_CALL_MODULES.md) | [ROADMAP.md](ROADMAP.md) | [VERIFICATION_STATUS.md](VERIFICATION_STATUS.md)

---

**Last Updated**: 2026-05 (intrinsics addition)
**Maintainer Rule**: Update on every trust-boundary-relevant code change.

### Call-summary storage observation

`DenoteExternalCalls.externalWorldOf` includes contract namespace **0**,
which has aliased the caller's unqualified storage since #2243. It is not
filtered out: doing so would hide callback/delegatecall writes from summary
postconditions and the staticcall preservation law. Positive namespaces
remain observable too. Namespace IDs are model identities, not a claim that
namespace 0 is the EVM address zero. This projection covers the `contractStorage`
view; it does not establish preservation of balances, transient storage,
events, or other state channels.

`Contracts.Examples.SummaryConformance` specifies an exact caller-slot update
on non-static calls and complete projected-storage preservation on static
calls. Its transaction example still executes real writes before rollback.
CI builds the entire `Contracts` library, including this conformance proof.

The pinned-corpus coverage tool uses separately checksum-pinned legacy solc
binaries solely to inventory unchanged upstream sources and their inheritance
chains. These do not become accepted `solidity_import` compiler versions.
Importability is measured by the actual Lean importer; coverage percentages
and first-blocker histograms neither establish EVM equivalence nor expand any
compiler proof boundary. Missing or failed measurements are reported explicitly.
