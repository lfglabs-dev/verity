# Architectural & Roadmap Review — GPT-6 Astra (`openai/gpt-6-astra`)

## 1.1 Closing the Last-Mile Pipeline Disconnects (`Codegen.lean`, `EndToEnd.lean`, and `EVMYulLean 2.0` Gas Unification)

Treat this as **proof-preserving integration**, not just additional code-generation passes. Without the source tree, the names below describe integration points rather than confirmed existing APIs.

### 1. `Compiler/Codegen.lean`: make certification part of the pipeline

- Have `CertifiedPatchPack` supply each transformation together with its applicability conditions and semantic-preservation theorem. Apply it through one checked interface; do not maintain a separate unchecked production path.
- Integrate `SlotCoalescingShim` at the storage-layout boundary, before lowering storage accesses. Thread its slot mapping through both code generation and the state-representation relation. Require proofs of non-aliasing—or sound packed-field masking where slots are intentionally shared—and preservation of observable storage behavior.
- Use `SelectorDispatchTree` when lowering ABI entry-point dispatch. Prove equivalence to the reference dispatcher, including short calldata, unknown selectors, fallback/receive behavior, and the project's selector-collision policy.
- Make pass order explicit and compose the certificates. If these components operate on different IRs, place them at their respective boundaries rather than forcing them into a single rewrite list.

A useful interface shape is:
```text
checked transform :
  input + preconditions → output + semantic-preservation evidence
```
Keep proof evidence out of emitted EVM code.

### 2. `EndToEnd.lean`: strengthen and compose the simulation

- Extend the end-to-end state relation to include the shim’s storage mapping and any new intermediate representations.
- Compose lowering correctness, dispatch equivalence, certified-patch preservation, and target execution correctness.
- State the theorem for the **actual exported compiler**, including enabled optimization options—not just the reference pipeline.
- Expose remaining assumptions explicitly: supported source fragment, ABI validity, layout validity, target fork, and gas conditions. Avoid placeholder axioms or `sorry` at integration boundaries.

### 3. Unify gas accounting with `EVMYulLean 2.0` `Gas.lean`

- Pin an exact dependency revision and EVM fork; first inspect the actual `Gas.lean` API.
- Make that module the authoritative source for gas types, schedules, and charging rules. Replace duplicated constants in `GasCostModel` with imports or a thin adapter.
- Distinguish **exact execution gas** from **compiler-side estimates/bounds**. Prove adapter equivalence for exact costs and soundness inequalities for estimates.
- Account for state-dependent charges: memory expansion, warm/cold accesses, storage transitions, refunds, and call forwarding—not merely opcode base costs.
- Keep functional correctness and gas refinement separate. A semantics-preserving optimization need not preserve behavior at identical finite gas because it can change out-of-gas outcomes. State sufficient-gas or budget-refinement hypotheses explicitly.

### 4. Acceptance checks

Require kernel-checked composition proofs, reference-versus-optimized execution tests, ABI/storage edge cases, and gas boundary tests against the pinned semantics. Finally, verify there is only one authoritative gas schedule and no exported code-generation path bypasses certification.

---

## 1.2 Completing Layer 2 Whole-Contract Completeness (`#1630`/`#1638`, `AdversaryModel`, Dynamic Arrays, EIP-1153, `#2082`)

Treat these as five proof/API alignment tasks, not as reasons to weaken the Layer 2 theorem. Without the current sources, the names below describe proof obligations rather than exact Lean signatures.

1. **Discharge helper correctness through the catalog.**
   - Define the invariant connecting helper calls emitted by compilation to entries in `SupportedHelperSummaryProofCatalog`: lookup succeeds, signatures agree, and the entry describes the **actual emitted helper IR**.
   - Prove `CompiledStmtStepWithHelpersAndHelperIR` by statement induction, using the corresponding catalog theorem in each helper-call case.
   - Cover transitive helper dependencies as well as direct calls; use an acyclic dependency ordering or a suitable well-founded execution argument.
   - Then remove **`helperSurfaceClosed` as a caller-supplied premise** by deriving the required closure/correctness facts from supportedness and catalog completeness. Do not simply delete the underlying obligation.

2. **Unify `AdversaryModel`.**
   - Put one canonical definition in a shared, dependency-light module; replace duplicate definitions with imports or temporary aliases.
   - Make both semantics use the same external-call outcomes and environment assumptions: return/revert data, state effects, callbacks/reentrancy, and any gas abstraction.
   - Quantify the simulation over one shared model, or an explicitly proved coupling of adversarial traces—not independently chosen source and IR outcomes.

3. **Make dynamic-array addressing identical on both sides.**
   - Share a slot-addressing definition:
     `base(s) = keccak256(encodeBytes32(s))`,
     `slot(s, i) = (base(s) + i) mod 2^256`.
   - Prove the lowering hashes exactly the 32-byte, big-endian slot encoding, then adds the index with EVM word arithmetic. Reconcile storage-length location and bounds-check behavior.
   - This formula is for **one-slot elements**. Either restrict supported arrays accordingly or separately prove packed-element offsets and multi-slot strides. Do not hash `s + i` or use mapping-style key encoding.

4. **Include `attachNonReentrantGuard` in `SupportedSpec`.**
   - Prove a preservation theorem for the guard transformation, including its emitted helper/IR obligations.
   - Model EIP-1153 transient storage explicitly: transaction-local lifetime, storage-context ownership, call-frame rollback, and `TSTORE` restrictions under static execution.
   - Verify entry check/set, cleanup on every normal exit, and rollback on revert; show guarded callbacks fail without disturbing unrelated state.
   - State the required EVM fork and reserved lock-slot assumptions. Establish simulation against a **guarded source specification**; the guard intentionally changes unguarded reentrant behavior.

5. **Finish dynamic event/error payloads with shared ABI proofs.**
   - Build or reuse one verified ABI encoder covering head/tail offsets, lengths, padding, concatenation, and nested dynamics **within the supported type subset**.
   - For errors, prove selector plus encoded arguments and exact `REVERT` byte range; argument offsets are relative to the argument block, excluding the selector.
   - For events, prove signature/indexed topics separately from non-indexed data. Indexed dynamic values require Solidity’s special in-place encoding and hashing, not ordinary ABI head/tail encoding.
   - Carry memory-layout, non-overlap, and size/overflow obligations through lowering.

**Finish line:** `SupportedSpec` plus explicit semantic assumptions implies Layer 2 simulation, with helper obligations derived internally and no new axioms or `sorry`s. Use differential EVM tests for layout and rollback edge cases as regression checks—not substitutes for these proofs.

---

## 1.3 Completing Layer 3 & Removing `solc` and `Import.lean` from the TCB

Treat this as three separate proof-boundary closures. **The target is a kernel-checked theorem about the exact deployed bytecode**, not merely about generated Yul. The names below refer to the interfaces in your question; exact obligations depend on their definitions.

### 1. Close `BridgedSafeStmts` over the whole helper environment

- **Freeze the complete helper table before proving safety.** Include compiler-generated helpers, transitive helper dependencies, and ECM shims. Check name uniqueness, resolution, arities, and absence of accidental shadowing.
- Prove an **environment-indexed closure theorem**: every reachable statement is bridged-safe, and every helper call resolves in that same environment to a body with the required semantic contract. Do not discharge calls using membership alone or a local table that can subsequently change.
- Handle the call graph explicitly: use topological induction for acyclic helpers; use a suitable recursive semantic relation or well-founded argument where recursion is supported. Do not silently assume termination.
- Require every `.proved` `VerifiedECMShims` entry to carry a kernel-checked proof connecting its **actual installed implementation** to its specification, including relevant state effects and exceptional behavior. A tag or proof about a different body is insufficient.
- Compose these into the whole-program compiler-correctness theorem. Keep unchecked shims outside the fully verified entry point, or expose them as explicit theorem assumptions.

**Deliverable:** a closed helper-environment certificate and a theorem deriving whole-program `BridgedSafeStmts`, with no unresolved helper/shim hypotheses.

### 2. Remove `solc --strict-assembly` from the TCB

Use `MetaSpec.DialectCommutation` as the **semantic composition boundary**, not as evidence that an arbitrary assembler is correct.

- Fix the supported Yul dialect, EVM revision, state relation, and observable behaviors. Account explicitly for memory/storage, calls, return/revert data, exceptional halts, and gas—or state precisely the abstraction under which gas is excluded.
- Establish the required Yul-to-EVM simulation/refinement and instantiate dialect commutation with it. Do not demand unrestricted bidirectional equivalence if only forward compiler correctness is needed.
- Choose either:
  1. **Verified assembler:** implement lowering and encoding with proofs covering helper lowering, stack layout, labels, jumps, opcode encoding, and code layout; or
  2. **Translation validation:** allow `solc` to propose bytecode and auxiliary certificates, but accept the result only after a sound, kernel-checked validator establishes the required Yul/EVM relation. Validation failure must reject the artifact, not fall back to trust.
- Bind the theorem to the **exact byte sequence deployed**, including constructor/init-code behavior and the runtime code it returns where applicable. Disable unsupported transformations or validate their results too.

**Deliverable:** a theorem connecting compiled Yul to concrete bytecode execution. `solc` becomes an untrusted producer; the relevant semantics, proof checker, and remaining explicit assumptions remain in the trust boundary.

### 3. Remove `SolidityImport/Import.lean` from the TCB through `SolcoreBridge`

- Make the importer an **untrusted producer** of the Verity representation plus an automated `CertifiedContractTranslationWitness`.
- Have `SolcoreBridge` check or reconstruct a proof relating the source contract’s semantics to that representation. Obligations should cover the supported subset’s typing, arithmetic, storage layout, ABI/dispatch, evaluation order, calls, and revert behavior.
- Generate routine obligations structurally and discharge them with proof-producing automation. Reject unsupported constructs and incomplete witnesses; do not replace missing proofs with axioms.
- Bind each witness to the **actual source representation and generated target**. If the theorem begins at a Solcore AST, parsing and Solidity-to-Solcore elaboration remain a boundary: verify or validate those steps, or explicitly limit the claim to that AST.
- Compose the witness with the helper-closure and bytecode-refinement theorems.

**Final acceptance criterion:** one theorem of the form
`source semantics ⟶ Verity semantics ⟶ Yul semantics ⟶ deployed EVM semantics`,
with compatible observations and explicit environmental assumptions. Audit its transitive axioms and artifact binding: neither an importer success flag, `.proved` label, nor successful `solc` execution closes a proof boundary by itself.

---

## 2.1 & 2.2 Real-World Ethereum Corpus Ingestion & 4-Way Differential Test Replay

Treat this as two connected projects: **a provenance-preserving Solidity frontend** and **a reproducible semantic conformance pipeline**. The names below describe proposed components, not verified APIs in your current tree.

## 1. Corpus ingestion and frontend expansion

### Build a pinned, reproducible corpus
- **Sourcify:** ingest verified compiler-input metadata and all referenced source files; retain chain ID, address, verification status, compiler version, optimizer settings, `viaIR`, EVM version, libraries, and constructor arguments where available.
- **Etherscan:** select deployments using a **dated, explicit TVL ranking**, then fetch verified sources and compiler settings. Treat TVL as prioritization, not semantic coverage. Resolve proxies to implementations at a pinned block; preserve both artifacts.
- Cover Uniswap v2/v3/v4, Aave, Morpho, and Curve as deployment families. Add **Solady and OpenZeppelin as version-pinned dependency/test suites**, not TVL-ranked protocols.
- Deduplicate by normalized compiler-input hash, while retaining deployment provenance. Cache inputs and artifacts; record licensing and respect API limits.
- Maintain a manifest per case:
  ```text
  provenance + source hashes + solc/settings + dependencies/linking
  + target fork + deployment fixture + supported-feature status
  ```
  A source bundle alone is insufficient to reproduce deployed behavior.

### Widen `Import.lean` by measured feature coverage
Run the importer over the corpus and generate a **structured unsupported-feature inventory**, ranked by frequency and dependency fan-out.

Prioritize:
1. Exact-width integers, signedness, casts, checked/unchecked arithmetic, evaluation order.
2. Inheritance/linearization, overload resolution, modifiers, libraries, interfaces.
3. ABI encoding/decoding, calldata/memory/storage distinctions, storage layout, mappings, arrays, structs.
4. Calls, return/revert data, errors, events, immutables, creation and linking.
5. Inline assembly and fork-specific facilities.

Use the matching `solc` AST/type information where practical rather than reimplementing Solidity name resolution. **Reject unsupported constructs explicitly**; never silently approximate. Keep source locations through `solidity_import → EmitVerity → compile`.

### Make `InlineAssemblyShims.lean` a semantic boundary
- Prefer a typed Yul representation and opcode semantics over textual substitutions.
- Give each shim an explicit contract: inputs, outputs, memory/storage effects, exceptional behavior, fork availability, and proof obligations.
- Cover arithmetic, memory, calldata/returndata, hashing, storage, logs, and call/create behavior incrementally.
- Model memory expansion, transient storage, warm/cold access, and newer opcodes only for supported forks.
- For narrowly recognized assembly idioms, validate their preconditions mechanically; otherwise fail closed.

**Deliverable:** a coverage dashboard distinguishing *parsed*, *imported*, *compiled*, *executed*, and *proved*. Passing execution tests must not be labeled verification.

## 2. Four-way differential harness

### Define the four lanes precisely
`solc` is a compiler, not an execution engine. A workable arrangement is:

| Lane | Execution |
|---|---|
| A — Solidity reference | Matching `solc` bytecode executed by a pinned reference EVM |
| B — source semantics | Imported program evaluated by Layer 1 `Denote` |
| C — intermediate semantics | Emitted Yul evaluated by EVMYulLean 2.0 `GasInterpreter` |
| D — target execution | Verity-compiled bytecode executed by pinned `revm` |

Verify the actual supported interfaces and forks of both Lean interpreters before implementing adapters. Prefer an independent engine for A; optionally run `solc` bytecode in `revm` as a control to separate compiler discrepancies from runtime discrepancies.

### Normalize inputs and observables
Define one serialized case format containing:
- Fork, chain/block/transaction context, caller/value/calldata.
- Initial accounts, balances, nonces, code, storage, access list, and gas limit.
- Deployment configuration and an optional transaction sequence.

Compare **status, return/revert bytes, ordered logs, persistent state changes, balances/nonces, and created contracts**. Normalize interpreter bookkeeping, not genuine EVM differences.

Separate three obligations:
1. **Functional equivalence** with sufficient gas.
2. **Gas accounting conformance** where semantic models support it.
3. **Out-of-gas/boundary behavior** at identical gas limits.

Do not require identical gas consumption between differently optimized implementations. Likewise, explicitly delimit or model code introspection, `gasleft()`, deployment-address differences, and other artifact-sensitive behavior; universal observational equivalence is not automatic.

### Adapt existing test ecosystems
- **Foundry/Hardhat:** reuse fixtures and tests through a common runner; lower host-side cheatcodes, snapshots, and mocks into explicit fixture actions. Mark unsupported host interactions rather than pretending they are EVM behavior.
- **EEST:** use execution-spec state fixtures to validate interpreter fork behavior and transaction semantics. Most arbitrary-bytecode EEST cases cannot run in source-level `Denote`; keep these as a runtime-conformance track.
- Add deterministic property-based generation of **supported Solidity programs** and ABI-valid, stateful call sequences. Include arithmetic boundaries, aliasing, ABI edge cases, revert propagation, and external-call interactions.

### Automate diagnosis and acceptance
For each case:
```text
pin inputs → compile/import → execute applicable lanes → canonicalize
→ compare → minimize mismatch → archive reproducer
```
Store seeds, tool versions, artifacts, traces, and the supported-feature/fork matrix. Minimize source programs, transaction sequences, and initial state; classify mismatches as importer, semantics, lowering, runtime, gas, or fixture errors.

**Rollout:** opcode/ABI microtests → OpenZeppelin/Solady subsets → isolated protocol components → complete pinned deployments. Run a small deterministic CI suite per change and the larger corpus nightly. Differential testing supplies counterexamples and regression evidence; Lean proofs establish equivalence only under their stated semantic assumptions.

---

## 2.3 & 2.4 Certified Gas Superoptimization (`maxwell` + `ShimArena`) & `solc` Bug Discovery Engine

Assuming `maxwell`, `ShimArena`, `CertifiedPatchPack`, and `EVMYulLean 2.0` refer to your project’s components, the plan below specifies their **roles and proof obligations**, rather than assuming particular APIs or existing guarantees.

## 1. Find gas losses, then synthesize certified optimizations

**Measure before choosing rewrites.** Benchmark identical contract semantics across Verity, `solc` Legacy, `solc --via-ir`, and hand-tuned Solidity/Solady implementations. Pin compiler versions, optimizer settings, EVM fork, calldata, initial storage, and warm/cold access state. Separate deployment cost, successful calls, reverting calls, and transaction-level refunds.

Likely sources of overhead—not established findings about Verity without measurements:

| Area | What to inspect |
|---|---|
| Storage | Redundant `SLOAD`s; repeated slot hashing; missed packing; unnecessary read-modify-write sequences |
| Memory/ABI | Repeated bounds checks, copying, allocations, zeroing, and conservative encoding/decoding |
| Word representation | Repeated masking/sign extension; failure to propagate known-bit and range facts |
| Control flow | Extra branches, generic dispatch, missed inlining, duplicated checks |
| Stack/code generation | Excessive `DUP`/`SWAP`, spills, poor expression ordering, missed constant folding |
| Specialized implementations | Solady-style assembly and layout choices that require stronger invariants than generic compilation |

Some gains require **representation or algorithm changes**, not local peepholes. Compare like-for-like semantics, including malformed-input behavior.

### Autonomous loop

1. **ShimArena:** run a deterministic benchmark corpus and collect instruction-level cost attribution, bytecode size, and semantic traces.
2. **maxwell:** propose bounded IR/Yul rewrites from a constrained grammar, guided by hot spots. Treat generated patches and proofs as untrusted.
3. **Cheap rejection:** type-check, validate effects, and run differential tests/property tests.
4. **Certification:** discharge `preserves_eval` and `improves_cost` in Lean against the pinned EVM semantics.
5. **CertifiedPatchPack:** package the rewrite, side conditions, proof terms, semantic-model version, tests, and benchmark evidence.
6. **Admission:** independently kernel-check proofs; accept only non-regressing candidates under a declared objective. Keep search sandboxed and changes reviewable/reversible.

**Make the proof statements precise:**

- `preserves_eval`: under explicit preconditions, preserve return/revert bytes, storage, logs, external-call behavior, and relevant execution outcomes—not merely the final arithmetic value.
- `improves_cost`: under the same preconditions and fork, establish a gas inequality over the modeled execution; state whether it concerns gross gas, refunds, deployment, or transaction-charged gas.
- Include aliasing, memory validity, storage effects, word-width facts, and stack constraints in rewrite side conditions.

**Gas is observable.** `GAS`, out-of-gas behavior, and EIP-150 call forwarding mean “same output, fewer instructions” does not imply unrestricted contextual equivalence. Define a gas-insensitive observation model, restrict applicable contexts, or prove an appropriately qualified refinement. Likewise, a Yul cost improvement is not automatically an EVM gas improvement: certify or measure the lowering and stack-allocation effects.

Start with constant folding, redundant normalization elimination, and effect-aware local simplifications. Delay storage caching and call-adjacent motion until the alias/effect model is strong enough.

## 2. Use differential validation to detect compiler correctness defects

Use this as an **isolated compiler-validation campaign**, not as a search for exploitable deployed contracts.

- **Define the shared subset.** A verified Verity pipeline is an oracle only for programs whose source semantics and translation into that pipeline are established. Merely translating Solidity into “similar” Verity code introduces another possible bug.
- **Generate well-defined test programs** with explicit initialization and controlled external-call stubs. Emphasize storage/memory reference relationships, narrow integers and normalization boundaries, and side-effecting expression sequencing.
- **Respect language latitude.** For evaluation order, compare against the source semantics’ permitted outcomes; do not flag differences where the language intentionally leaves order unspecified.
- **Compile and execute** the same supported semantics through Verity, Legacy, and `--via-ir`, using pinned configurations and a common EVM execution harness.
- **Compare semantic observations**—status, return data, persistent state, logs, and call traces—separately from gas. Gas differences alone are not compiler correctness bugs.
- **Triangulate divergences.** Check translation assumptions, compiler settings, runtime behavior, and the verified model before attributing a mismatch to `solc`. Agreement between two pipelines is not proof that the third is wrong.

### Automated reduction

For a detected mismatch, use syntax- and type-aware delta debugging to minimize the **compiler regression testcase**: remove functions, statements, expressions, inputs, and initial-state entries while preserving defined behavior and the same semantic discrepancy. Require deterministic replay and maintain the relevant aliasing/width/sequencing conditions throughout reduction.

Produce a maintainer-facing artifact containing:

- minimized source and input state;
- exact compiler versions, flags, and EVM fork;
- expected semantic observation and its justification;
- actual observations and a focused trace;
- relevant proof assumptions and translation boundary.

The key distinction: **certified optimization proves a transformation under stated assumptions; differential testing supplies evidence of a disagreement.** Calling that disagreement a `solc` bug still requires showing that its output violates the applicable source semantics.
