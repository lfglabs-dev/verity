# Audit Registry

This file records trust-boundary changes and the evidence that keeps them
reviewable. Keep it synchronized with `TRUST_ASSUMPTIONS.md` and `AXIOMS.md`
whenever semantics, trusted components, generated audit artifacts, or CI
boundary checks change.

## Current Audit State

- Lean proof placeholders: 0 `sorry` in compiler/proof modules.
- Project-level Lean axioms: 0. See `AXIOMS.md`.
- Authoritative safe-body Yul runtime target: pinned `lfglabs-dev/EVMYulLean`.
- The previous reference-comparison modules have been removed from the live
  proof tree; native EVMYulLean is the checked runtime boundary.
- Yul-to-bytecode compilation remains trusted through pinned `solc` 0.8.33.
- Consumer-declared intrinsics are consumer-owned trust boundaries. The CLZ
  prototype keeps Verity at 0 project-level axioms and requires downstream
  packages to document any assumed intrinsic obligation they declare.
- Gas safety is not modeled by the semantic preservation theorems.

## Issue #1722: EVMYulLean Semantic Target

Status: full semantic integration for safe compiler-produced bodies.

### Event Emission Proof-Model Alignment (2026-06)

Source-semantics `normalizeEventValue` (Compiler/Proofs/IRGeneration/SourceSemantics.lean)
now includes a `.newtypeOf _ baseType => normalizeEventValue baseType value` arm, mirroring
the compiler's newtype erasure in `normalizeEventWord` (Compiler/CompilationModel/EventAbiHelpers.lean).
This proof-model alignment ensures that source event values normalize consistently with
compiled event word normalization for scalar newtype parameters. Affects the event proof
path only (non-events statements are unchanged).

New proof module `Compiler/Proofs/IRGeneration/GenericInduction/EventBridge.lean` bridges
scalar event emission semantics, discharging the `EventHeadStepSemanticBridgeCatalog.bridge`
obligation with per-statement step lemmas, memory wrapping facts, and normalized-word
equivalence theorems. Proof-only scaffolding; no compiler output changes.

The current generic scalar-event slice is intentionally top-level only: supported
`emit` statements may appear as function-body heads with scalar parameters and at
most three indexed parameters. The contract-level scalar-events wrapper now lifts
the function-level proof over dispatch when callers supply the scalar-event
list-interface witnesses, and `ContractFeatureTest.lean` includes a top-level
emit smoke contract. Nested emits inside structural statements remain future
work, and the Yul/EndToEnd proof layers still exclude event/log semantics.

### Compiler-Side Emit-Argument Scope Collection (2026-06)

`collectStmtNames` (Compiler/CompilationModel/ValidationHelpers.lean) emit arm now returns
`collectExprListNames args` rather than `eventName :: collectExprListNames args`. Event
argument expressions now participate in scope-name collection for statement sequence
validation; the event name itself is resolved against the event table and does not enter
the identifier scope. Enables scope-aware event argument validation without shadowing
event name resolution.

### Proof-Side Scratch Memory Wrapping (2026-06)

Memory-access functions in the proof IR model now wrap byte/word offsets modulo `2^256`
to match compiled code's wrapping `add` builtin semantics. Affected functions:
- `memorySliceWords` (IRInterpreter.lean): word-reading offset wrapping
- `yulLogDataWords` (IRInterpreter.lean): log data extraction offset wrapping
- `writeEventSignatureScratchFrom`, `writeUnindexedEventScratchFrom` (SourceSemantics.lean):
  scratch memory write offset wrapping

Ensures proof-side scratch addressing matches compiled emit block's offset arithmetic
under EVM `Uint256` wrapping, preventing false misalignment in the semantic bridge.

The EVMYulLean transition moved the safe-body EndToEnd runtime target from
Verity-owned Yul builtin scaffolding to native EVMYulLean runtime execution.
The current proof surface has:

- 36 of 36 builtin bridge theorems proven.
- 0 admitted bridge lemmas.
- `smod` and `sar` bridge equivalences fully discharged.
- `compileStmtList_always_bridged` proven for `BridgedSafeStmts`.
- Public native EndToEnd wrappers whose runtime target is
  `EvmYul.Yul.callDispatcher`.

The external-call/function-table family
(`internalCall`, `internalCallAssign`, `externalCallBind`, and `ecm`) now has
function-table-aware closure scaffolding in
`Compiler/Proofs/YulGeneration/Backends/EvmYulLeanCallClosure.lean`. The
public surface — `BridgedSourceInternalCallStmt`,
`BridgedSourceExternalCallBindStmt`, `BridgedSourceEcmStmt` (with the
per-module `ECMBridgeable` obligation), and the corresponding
`compileStmt_*_bridged` / `compileStmtList_*_bridged` closure theorems —
discharges `BridgedStmts` against a `BridgedFunctionTable`. The composition
lemma `BridgedStmts_of_compileStmtList_append` lets concrete contracts
chain these closures with `compileStmtList_always_bridged` across an
arbitrary `pfx ++ sfx` split. End-to-end smoke proof in the same file.
Wiring of `SupportedFragment` / `SupportedSpec` for contracts that
actually use this family is the next milestone.

## Reentrancy Rely-Guarantee Framework (2026-06)

A new proof-level reentrancy framework, complementary to the runtime
`nonreentrant` transient-storage guard (#1893). Additive and axiom-free; it
keeps the "Project-level Lean axioms: 0" invariant above.

- **New modules** (no `sorry`, no `axiom`, no `native_decide`):
  - `Verity/Core/Invariant.lean` — state-polymorphic rely-guarantee library
    (`Preserves` / `runSeq` / `runSeq_preserves`).
  - `Verity/Core/Reentrancy.lean` — grounds it against the `Contract` monad:
    `reentrantCall`, `ContractPreserves`, `ReentrancySpec` and the
    whole-interleaving meta-theorem `ReentrancySpec.schedule_preserves`, plus a
    forward-compatible multi-contract layer (`System` / `lift` / `Isys` /
    `cross_contract_schedule_preserves`).
- **New semantic surface**: `Env.reenter : ContractState → ContractState`
  (default `id`, the no-reentry case) on `Verity/Core/Semantics.lean`.
- **Worked example**: `Contracts/ReentrancyRelyGuarantee` machine-checks the
  Midnight `take`/`liquidate` callback bug — the no-lock `take` admits a
  permanent bad-debt liquidation; the locked `take` admits none for any
  lock-respecting adversary.
- **Trust boundary**: author obligations (entrypoint-registry completeness,
  adversary-model fidelity, invariant adequacy). See the
  "Reentrancy Rely-Guarantee Framework" section in `TRUST_ASSUMPTIONS.md`.
- **CI state**: the example is registered in `test/property_manifest.json` and
  classified proof-only in `test/property_exclusions.json` (abstract
  state-transformer proofs, no compiled bytecode to property- or
  differential-test); structure/Foundry-test exemptions are recorded in
  `scripts/check_contract_structure.py`. `artifacts/verification_status.json`
  and `docs/VERIFICATION_STATUS.md` now record 15 example contracts and +8
  proven theorems (all proof-only, so runtime coverage moves 90% → 88% by
  construction while proven count rises 283 → 291).

### Cross-Function Reentrancy Gate (fail-closed)

A compilation-level gate that complements the proof framework above:
`validateReentrancyDisposition`
([Compiler/CompilationModel/Validation.lean](Compiler/CompilationModel/Validation.lean)),
a dedicated pass run after call well-formedness validation (and independent of
the single-function CEI check in `validateFunctionSpec`),
now **rejects** any non-`view`/`pure` function whose body makes a direct
external call unless it carries a sound reentrancy disposition. This closes the
cross-function reentrancy class (Midnight `take`/`liquidate`) at the toolchain
boundary: a CEI-clean function is no longer enough, because its external
callback still leaves a transiently-exploitable state live for a reentrant
sibling entrypoint.

- **Accept-set** (sound only): `nonreentrant(<lock>)` (runtime transient-storage
  guard, #1893) or `reentrancy_trusted` (new metadata-only, unproven author
  assertion — emits no code, no proof obligation, recorded as a trust boundary).
- **Deliberately rejected**: `cei_safe` and `allow_post_interaction_writes`
  concern single-function CEI ordering only and do **not** satisfy the gate.
- **Internal-helper closure** (Bugbot HIGH on #2032): the `nonreentrant(<lock>)`
  transient guard is attached **only** at the external dispatch boundary
  (`attachNonReentrantGuard`, #1893), so it is absent on the lock-free
  internal-helper shadow the macro emits for direct intra-contract calls. A
  *lock-only* `nonreentrant` function (no `reentrancy_trusted`) is therefore
  **rejected when invoked as an internal helper** at macro lowering
  (`ensureCallableAsInternalHelper`,
  [Verity/Macro/Internal.lean](Verity/Macro/Internal.lean)); routing such a call
  through the shadow would run the guarded body without the lock and silently
  bypass its only protection. A callee that *also* carries `reentrancy_trusted`
  is accepted (the assertion covers the lock-free internal path). This mirrors
  the existing `internal nonreentrant(<lock>)` rejection
  (`NonreentrantInternalHelperRejected`, #1971).
- **CEISafety demoted**: `Compiler.Proofs.IRGeneration.CEISafety`
  (`CEIProofBackedExecution`) remains a valid proof surface, but it certifies
  *single-function* Checks-Effects-Interactions ordering — it is **not** a
  reentrancy defense and is no longer presented as one. Cross-function
  reentrancy safety is owned solely by this gate's accept-set
  (`nonreentrant`/`reentrancy_trusted`); CEI is subordinate ordering hygiene.
- **New annotation surface**: `reentrancy_trusted` threads through the macro
  (`Verity/Macro/Syntax.lean` → `Translate/Parsing.lean` → `Types.lean` →
  `Translate.lean`) onto `FunctionDecl.reentrancyTrusted` /
  `FunctionSpec.reentrancyTrusted` (defaulted `false`, backward compatible).
- **Regression evidence**: `Contracts/Smoke/SecurityCombos.lean` pairs
  `ReentrancyDispositionRequired` (a CEI-clean `take` rejected by the gate,
  pinned with `#guard_msgs`) against `ReentrancyDispositionDeclared` (the
  identical body accepted once it declares `reentrancy_trusted`) — identical
  bodies, opposite verdicts, the Midnight shape proven unable to pass
  `#check_contract` undeclared.
- **Axiom-free**: the gate is a pure validation predicate; `AXIOMS.md` is
  unchanged. Trust-boundary prose is in the "Cross-Function Reentrancy Gate"
  section of `TRUST_ASSUMPTIONS.md`.

## External-Call Journal (2026-08)

- `ContractState.calls` (`Verity.ExternalCall` entries) is a new append-only,
  defaulted field: a proof-side observable of external-call boundaries, not
  EVM state. No semantic-preservation claim covers it.
- `DenoteExternalCalls.denoteCall` is unchanged; the journal is added by the
  definitionally layered `denoteCallJournaled` / `denoteJournaled`, so all
  previously proven world/gas/rollback laws hold verbatim.
- Source-level observation is `DenoteExternalCalls.externalCall :
  AdversaryModel → CallSite → Contract ExternalCallResult`
  (`Verity/Core/Model/ContractExternalCall.lean`), which reports
  callee failure/revert in-band and never raises a monadic revert;
  `externalCallRequireSuccess` opts into bubbling snapshot rollback.
- Semantic choices (journal survives caller-side rollback; adversary cannot
  write the journal) are documented in `TRUST_ASSUMPTIONS.md` §"External-Call
  Journal".
- **Axiom-free**: `AXIOMS.md` unchanged.

## FunctionSpec Calls, ETH Value, Multi-Contract World (2026-08)

- `Denote.evalExpr` / `execStmt` still map `Expr.call` and
  `Stmt.externalCallBind` to `none` / `.revert`, so
  `DenoteAgreement` stays definitional against `SourceSemantics`.
  The widened fragment is `Verity.Core.Model.DenoteFunctionCalls`:
  `evalExprCall` / `execExternalCallBind` take a `CallEnv`
  (`AdversaryModel` + link-time target / value / siteId), debit
  `selfBalance` only on a successful `call`, and journal the real
  target and value.
- Base `withTransactionContext` is unchanged (keeps
  `DenoteAgreement` / `_frame_holds` stable). Payable calls use
  `withPayableCallContext`, which credits `selfBalance` with
  `msg.value`. `MultiContract.withCallContext` does the same on
  each hop.
- EDSL `Contracts.externalCallBind` stays name-keyed (`target`/`value`
  = 0). `externalCallBindTo` records target and value and debits ETH
  on success. Callee state is not in that single-world stub.
- `Verity.MultiContract` is a finite `Address → ContractState` world
  with ETH-valued hops. The P-ETH-1 ensemble is
  Bus → Gateway → Vault → (Lido | request). Model-plane only: those
  names are not compiled contracts and not an L2 claim.
- Zero new axioms.

## Execution-Backed External Call Frames (2026-08)

- `MultiContract.CallFrame` retains distinct caller-before, callee-before, and
  callee-entry states. `callEntry` checks distinct accounts, `call` kind,
  target/address agreement, and sufficient caller balance before producing a
  frame.
- `MultiContract.executeCall` consumes a `CalleeExecution`; its produced
  control and returndata determine commit/rollback and the journal entry.
  Success commits the caller debit and callee post-state. Failure/revert
  preserve both snapshots (apart from the caller's append-only observation).
- `DenoteFunctionCalls.executeFunctionWithCalls` retains the FunctionSpec
  post-world and execution control. `runFunctionInFrame` is the first
  source-shaped adapter into the framed boundary; `callFunction` is the
  official checked composition and does not accept a separately supplied
  observation or post-state. The legacy `DenoteResult` projection is derived
  from the same execution.
- This slice deliberately supports ordinary `call` only. `staticcall` and
  `delegatecall` need distinct frame invariants before admission.
- Zero new axioms.

## EDSL Executable Plane: Linked External Calls Journal (2026-08)

- The EDSL executable stubs for linked external calls are no longer silent:
  `Contracts.externalCallBind`, `Contracts.callResultWords`,
  `Contracts.tryExternalCallWords`, and the `safeTransfer`/`safeApprove`
  family now append a `Verity.ExternalCall` entry to `ContractState.calls`
  (via `Contracts.linkedCallEntry`/`recordLinkedCall`). Previously they were
  `pure ()`-shaped no-ops, so any executable-plane theorem "about" an
  external call was vacuously insensitive to duplicated, omitted, reordered,
  renamed, or argument-mutated calls.
- General linked externals are name-keyed (address bound at link time), so
  `ExternalCall` gained a defaulted `name : String := ""` field; model-plane
  entries (`DenoteExternalCalls.journalEntry`) leave it `""` and are otherwise
  unchanged. Their executable-plane `siteId`/`target` are `0`. ERC-20 write
  wrappers instead record the token address as `target` and the actual wrapper
  arguments (excluding that target) as `calldata`; all retain the wrapper name.
  Journal position records call order.
- `ExternalArg.toWords` is a canonical, content-preserving journal encoding:
  scalars occupy one word, while arrays and byte arrays carry a length prefix
  followed by every recursively encoded element/byte. It deliberately does not
  claim byte-for-byte EVM ABI layout, but unlike the former size-only word it
  distinguishes same-length content mutations.
- In-band results remain deterministic stubs (`externalCallStubWord`);
  `callResultWords` and successful `tryExternalCallWords` with a supported
  single-word result decode and return the same word recorded in journal
  returndata. Aggregate/no-result executable stubs retain their inhabited
  default, as do failures. Both report
  `success := (name != "fail")` (`externalCallStubSuccess`), giving specs a
  reserved name to exercise failure paths. `externalCallWords` (the pure
  expression form) still returns the stub word without journaling — it is
  not monadic and cannot observe state; this remaining gap is documented in
  `TRUST_ASSUMPTIONS.md`.
- The model plane (`DenoteExternalCalls`, `ContractExternalCall`,
  `ExternalCallResult.control`) is untouched; all its laws hold verbatim.
- Discriminating evidence: `Contracts/Smoke/ExternalCallObservability.lean`
  separates duplicated/omitted/reordered/renamed/zeroed-arg and equal-length
  dynamic-content mutants over arbitrary pre-states, pins returned-value /
  returndata agreement and ERC-20 targets/calldata, and pins the
  revert-rolls-back-journal behaviour of `Contract.run`.
- **Axiom-free**: `AXIOMS.md` unchanged.

## Guarded Event Preservation + Checked Arithmetic Completion (2026-08)

- `Compiler/Proofs/IRGeneration/GuardedScalarEvents.lean`:
  `compile_preserves_semantics_guarded_with_scalar_events` closes final-result
  event preservation (`encodeEvents source.events = ir.events`) for the
  guarded whole-contract pipeline on the scalar-event fragment, by proving
  the guarded source semantics collapses to the plain one when every
  dispatched function is lock-free (which `SupportedSpecWithScalarEvents`
  forces). Pure composition of the #2000 event lane and the #2314–#2317
  guarded family; no new semantic assumption, no axiom.
- The `notModeledEventEmission` trust slice and `--deny-event-emission` gate
  are **kept**: they flag `rawLog`, which remains unmodeled. Known limit
  (documented in `TRUST_ASSUMPTIONS.md` §Event Emission): the slice does not
  enumerate declared `Stmt.emit` sites outside the scalar fragment; that
  boundary is enforced at the theorem support witness instead.
- `Verity/Core/Uint256.lean`: `checkedSub`/`checkedMul` + `subNoWrap`/`mulNoWrap`
  complete the checked-arithmetic lane (#1993) alongside `checkedAdd`.

## Audit Artifacts

| Artifact | Purpose | Check |
|----------|---------|-------|
| `artifacts/evmyullean_native_lowering_report.json` | Native lowering coverage, admitted bridge lemmas, safe-body integration status | `python3 scripts/generate_evmyullean_native_lowering_report.py --check` |
| `artifacts/evmyullean_fork_audit.json` | Pinned fork divergence and non-semantic fork delta | `python3 scripts/generate_evmyullean_fork_audit.py --check` |
| `artifacts/evmyullean_capability_report.json` | EVMYulLean capability surface and reference-oracle paths | `python3 scripts/generate_evmyullean_capability_report.py --check` |
| `artifacts/storage_layout_report.json` + `artifacts/STORAGE_LAYOUT_SUMMARY.md` | Per-contract storage layout for migration/audit review: explicit slots, alias ranges, reserved ranges, packed subfields, mappings, dynamic arrays, opt-in namespaces (#1897) | `python3 scripts/generate_storage_layout_report.py --check --no-lean` (drift gate in `make check`); regenerate with `make regen-storage-layout-report` |
| `PrintAxioms.lean` / generated axiom report | Axiom dependency visibility | `python3 scripts/generate_print_axioms.py --check` and `lake build PrintAxioms` |
| `Compiler.Proofs.IRGeneration.IntrinsicProofs` | Proven Verity-owned intrinsic plumbing: scope accounting, generic lowering shape, fork-order facts, and arity rejection | `lake build Compiler.Proofs.IRGeneration.IntrinsicProofs` |
| Intrinsic fork gate | Fail-closed `min_fork` enforcement against `--target-fork` / `YulEmitOptions.targetFork` | `lake build Compiler.CompileDriverTest` |
| `trust_report.intrinsics[*]` | Planned consumer-declared intrinsic trust surface: name, emission mode, opcode/builtin target, obligation, `min_fork`, and source location | Follow-up hardening; until then, grep consumer trees for `verity_intrinsic` |

## Storage-Lens API Freeze — C5 Step 1 (2026-08)

- `scripts/check_storage_lens_freeze.py` (in `make check`) ratchets raw
  `ContractState` storage-channel record updates: new
  `{ s with storageMap := ... }`-style sites fail CI; the 304 existing sites
  are frozen per file in the script's `BASELINE` and must only shrink.
  Exactly-lens-shaped helpers (`setLock`, `ReentrancyExample.setStorageSlot`/
  `setMappingSlot`, adversary transitions in the call-program examples,
  `TypedIRCompilerCorrectness` typed-IR write helpers) are already migrated
  to `writeSlot`/`writeMap`/`writeTransient`.
- This is step 1 of the C5 storage-representation flip (single word-addressed
  map + Solidity-layout slot derivation under stable lens names); steps 2–4
  (proofs onto `storage_simps`, representation flip, compiler slot
  correspondence) are tracked in `docs/ROADMAP.md`. No semantic change: the
  lenses are definitionally the former raw updates.

## Storage-Lens Simp Flip — C5 Step 2 (2026-08)

- The ContractState lenses are no longer default-`simp` transparent: the
  global `attribute [simp]` block in `Verity/Core.lean` is removed.
  `storage_simps` stays laws-only (read-over-write normalization; it
  deliberately does not unfold lenses to the raw record representation, so it
  survives the step-3 flip). Proofs that genuinely need the current raw
  representation now name the lens explicitly in their `simp` lists
  (`simp [ContractState.writeSlot]`) — those call sites are the step-3
  burn-down inventory, greppable as `ContractState.read`/`ContractState.write`
  occurrences inside simp lists.
- Repair surface: ~25 files (Core storage-array run-lemmas, Stdlib
  Automation/MappingAutomation, NonReentrantGuard, the `denote_stmt_arm`
  macro in `DenoteAgreement`, the `simp_tir_eval` macro in
  `TypedIRCompilerCorrectness`, and the contract proof suites). No theorem
  statement changed; no semantic change; zero axioms.

## StorageKey Canonical Backing — C5 Step 3 (2026-08)

- `ContractState` now stores word-valued channels in one
  `storageWords : StorageKey → Uint256` map. `StorageKey` is an injective
  inductive (`slot` / `contractSlot` / `transient` / `addr` / `map` /
  `mapUint` / `map2`). Solidity keccak slot derivation stays on the
  compiler side; lens laws use constructor injectivity, not hash
  injectivity.
- Public accessors keep the old names (`storage`, `storageAddr`,
  `storageMap`, …). Specs that read those views do not change shape.
  `storageArray` and `knownAddresses` remain separate fields this step;
  independence from the word-channel lenses is now proved
  (`Compiler.Proofs.Storage.SeparateChannels`).
- The freeze baseline shrinks to `Verity/Core.lean` (lens
  implementations) plus `Contracts/TypedIRTests.lean` (IRState field-name
  collisions). `storageWords :=` is forbidden outside `Verity/Core.lean`.
- C5 step 4 complete under `solidityMappingSlot_injective`
  (not axiom-free): `Compiler.Proofs.Storage.MappingCoherence`
  now defines `storageKeySlot` and address-keyed `MappingCoherent`,
  with `defaultState_mappingCoherent` / `MappingCoherentUint` /
  `MappingCoherentMap2` and the aligned `writeMap`/`writeMapUint`/
  `writeMap2`+`writeSlot` laws (same pair, plus other pairs under an
  explicit non-alias hypothesis). `FieldStorageKey` collapses a
  CompilationModel field list to a root `StorageKey` (and typed
  `map` / `mapUint` / `map2` entries) and proves `storageKeySlot`
  of that key is the resolved slot. Finite-set address
  `MappingCoherentOn` is preserved by an aligned write under an
  explicit pairwise derived-slot certificate
  (`MappingCoherenceOn`), including uint and nested-address lists.
  Address-keyed `mappingStruct` / `mappingStruct2` members collapse
  to `mappingSlotLocation` / `nestedMappingSlotLocation`. Compatibility
  `aliasSlots` are extra compiler write targets; the resolved head is
  the field's `storageKeySlot`. Cross-channel finite-set preservation
  (aligned write on one mapping channel vs another channel's list)
  takes an explicit derived-slot inequality. Packed subfields extract
  from the `storageKeySlot` word (`packedExtract`); compiler packed-read
  composition with SolidityStorage is `fieldPackedExtract_eq_compiledPackedRead`
  (`width < 256`). `FieldCoherence` identifies a named mapping field's
  `storageKeySlot` with the flat slot `MappingCoherent*` /
  `MappingCoherentOn*` reads.
  A lone `writeSlot` preserves a finite `*On` list under an explicit
  listed-vs-written slot inequality. A lone `writeTransient` preserves
  the same lists by constructor injectivity (`StorageKey.transient`
  vs persistent `.slot` / `.map` / `.mapUint` / `.map2`); no slot
  inequality. Global aligned `writeMap` / `writeMapUint` /
  `writeMap2`+`writeSlot` preserves `MappingCoherent*`.
  `writeTransient` preserves the globals by constructor injectivity.
  A lone `writeSlot` preserves a global under an explicit
  image-avoidance `∀` (derived slot ≠ written word). That `∀` is
  discharged for writes that never touch `StorageKey.slot`:
  `writeTransient` (constructor injectivity), `writeAddrSlot`
  (constructor injectivity of `.addr`), and `writeArray` (separate
  `storageArray` field). Finite `*On` lists lift from the globals
  without a pairwise certificate. Arbitrary `n` is still not claimed
  safe for a lone `writeSlot`.
  `FieldEncode` derives `findResolvedFieldAtSlot` from
  `findFieldWithResolvedSlot` plus no write-slot conflict, persistent,
  and unpacked, then identifies that slot with `encodeStorageAt`.
  An unoccupied mapping-derived slot (address, uint, or map2) encodes
  as the `MappingCoherent*` / `MappingCoherentOn*` shadow. bytes32-keyed
  maps collapse to `solidityMappingSlot` of the 32-byte word (no
  `StorageKey.mapBytes32`). All nine `MappingType.nested` key-type
  pairs collapse to `abstractNestedMappingSlot`.
- Zero new axioms.

## CI Guards

- `make check` validates generated reports, bridge coverage synchronization,
  builtin bridge matrix synchronization, Lean hygiene, proof length, and
  documentation counters.
- `make test-evmyullean-fork` validates the pinned fork audit, checks the
  native lowering report, rebuilds the public EndToEnd EVMYulLean target, and
  runs the concrete bridge-equivalence tests.
- `.github/workflows/evmyullean-fork-conformance.yml` runs the EVMYulLean fork
  conformance probe weekly. Scheduled or manual failures fail the workflow and
  open or update a GitHub issue for drift triage.
- Intrinsic fork enforcement is fail-closed: builds using an intrinsic whose
  `min_fork` exceeds the contract target fail unless the caller passes
  `--allow-future-fork-intrinsics`.

## Update Checklist

1. Update `TRUST_ASSUMPTIONS.md` for the human-readable trust boundary.
2. Update `AXIOMS.md` if axioms, non-axiom trusted primitives, or soundness
   controls changed.
3. Update this file with the changed audit state, artifacts, and CI guards.
4. Regenerate deterministic artifacts with the relevant `scripts/generate_*.py`
   command.
5. Run `make check`; run targeted Lean builds for changed proof modules.

**Last Updated**: 2026-06 (cross-function reentrancy gate: fail-closed `validateReentrancyDisposition` rejection of external-call functions lacking a sound disposition, new `reentrancy_trusted` metadata annotation, CEISafety demoted to single-function ordering hygiene, `#guard_msgs` regression pair in `SecurityCombos.lean` — axiom-free; reentrancy rely-guarantee framework: `Verity.Core.Invariant` / `Verity.Core.Reentrancy`, `Env.reenter` hook, Midnight `take`/`liquidate` worked example — additive, 0 axioms; event emission proof-model alignment, emit-argument scope collection, scratch memory wrapping; storage layout audit artifacts, #1897; nonreentrant transient-storage guard, #1893; non-alias certificate write-set overlap, #1967; nonreentrant fork requirement, #1968)
