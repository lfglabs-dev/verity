# Differential validation of Solidity slices

The reusable engine lives in Verity. A consumer supplies a JSON fixture naming
its source/signature, scalar input domains, argument projections, storage recipes
and fixed regression corpus. No consumer arithmetic is reimplemented in the engine.

## Execution contract

Every case takes three paths:

- **A:** original Solidity, compiled by checksum-pinned solc, deployed and called in Foundry.
- **B:** the imported `CompilationModel`, executed by the same `Denote.execStmtList`
  used in the proofs, with Verity's pure Keccak engine for storage slots.
- **C:** that model compiled by the normal Verity compiler, compiled from Yul by
  the pinned solc, deployed and called in the same Foundry harness.

Python constructs source calldata with `eth-abi` and storage slots with
`eth-hash`; it does not share Verity's encoders or arithmetic. Ignored ABI members,
including dynamic arrays, receive deterministic noise. Unused packed bits,
adjacent storage words, keys and unrelated slots are varied too. Each EVM case
uses a restored snapshot. V1 accepts read-only slices, rejects any recorded
storage write, and compares the initialized/observed storage words on all paths.
This is not a test of arbitrary state-writing contracts.

The comparator checks success/revert, exact scalar return words and observed
storage on A/B/C, plus exact return/revert bytes on A/C. B does not expose panic
payloads. Model calldata is the explicit scalar projection, not a claim that
Verity implements the complete source ABI. Gas and internal memory allocation
identity are not equivalence criteria. Resource exhaustion, invalid input,
unsupported compilation and tool failures are **harness errors**, never reverts.

The root must have a public/external ABI, static scalar returns, no constructor
arguments and the Osaka profile. Missing support is rejected before comparison.
The driver refuses uncovered models and does not interpret unknown constructors
through Denote's fallback. `keccakMemorySlice` is unreachable in this whitelist.

## Commands

Run from a Lake workspace (Verity or a downstream project):

```sh
scripts/check_solidity_differential.sh \
  --config Contracts/SolidityImportSmoke/differential.json \
  --output .lake/differential/smoke --seed 2438 --cases 128

scripts/check_solidity_differential.sh \
  --programs 5 --cases 16 --seed 2438 --output .lake/differential/programs

scripts/check_solidity_differential.sh \
  --mutations --output .lake/differential/mutants
```

Downstream projects invoke the same script from their pinned Verity dependency.
The script installs its Python dependencies in the caller's `.lake` directory.
The ordinary proof build has no Python package dependency.

Each generated expression is run directly and through hygienic renamed/helper
variants, including a scalar projection whose name collides with the temporary
prefix. The grammar exercises uint8/16/128/248/256 casts, checked arithmetic,
ternaries and helper composition. Independent source executions must agree
between metamorphic variants as well as between A/B/C. A metamorphic mismatch
is recorded in `metamorphic-divergence.json` with the differing source rows;
it is investigated directly rather than by the input reducer.

## Failure evidence and reduction

A campaign records the config, seed/values, materialized inputs, source closure,
solc inputs/outputs, generated Yul, both creation bytecodes, tool versions,
implementation/source hashes, import digest, logs and per-route results.
Fresh imports are checked against the recorded digest; changed implementation
or binary artifacts invalidate replay. The original workspace/toolchain is
required for replay; archived sources support auditing and reconstruction.

```sh
scripts/check_solidity_differential.sh --replay --output .lake/differential/smoke
scripts/check_solidity_differential.sh --reduce --reduce-seconds 120 \
  --output .lake/differential/failing-campaign
```

The reducer preserves the mismatch category, not merely any failure. It reduces
inputs, and additionally reduces the typed expression tree for generated programs.
It does not delete text from arbitrary production Solidity. Original evidence is
retained; reduced cases go in a child directory. Reduction is budgeted and does
not claim a globally minimal counterexample.

Mutation campaigns copy sources and create private copy-on-write build caches;
only dependency packages are shared. They compile actual importer and Denote
mutants. A changed comparison, wrong field slot, wrong packed mask and wrong
storage read must produce runtime divergences. A compile error/timeout is an
**invalid mutant**, not a detected semantic bug. Mutation outputs must be fresh.

## Extension and rollout policy

1. Keep the fixed source/case corpus and existing five Midnight proofs green.
2. Add positive, boundary, interaction and explicit-rejection cases for each new
   supported construct. Add a runtime-killed mutant where the risk warrants it.
3. Run fixed seeds on PRs; longer seeded input/program/mutation campaigns on a
   schedule and manually. Record every seed and publish failure artifacts.
4. Turn minimized counterexamples into reviewed, permanent regressions.
5. Keep importability, Denote coverage, compilability, compiler-proof coverage
   and tested observables separate. No test count establishes source equivalence.

The implementation sequence is shared protocol/A-B-C runner; input fuzzing and
consumer integration; generated programs/reducers; mutation checks and CI gates.
The initial PR/nightly budgets are 10/60 minutes excluding toolchain preparation;
CI timeouts are failures, not truncated passing campaigns.

## EVMYulLean assessment

The pinned dependency has a bytecode executor, `EvmYul.EVM.Ξ`, with explicit
execution exceptions including fuel exhaustion. The in-repo native harness is
primarily a Yul semantic/proof harness, not a drop-in runner for these deployed
bytecodes. A fourth path needs a concrete account/block/calldata setup, fork and
opcode conformance checks, independent return/revert/exception decoding, and
cross-checks against Foundry. It is not claimed as executed by this harness.
A/B/C is the implemented gate; adding D must not replace independent Foundry
execution or collapse an unsupported opcode into a contract revert.
