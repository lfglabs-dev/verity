# Solidity import

`solidity_import` turns selected Solidity functions, and the helpers they
reach, into an ordinary Verity `CompilationModel`. The model runs on the same
`Denote` semantics as Verity's proofs, so theorems about it are theorems about
the imported code. The importer lives in `Compiler/SolidityImport/`; the
Midnight pilot (`lfglabs-dev/morpho-midnight-verity`) is the reference user.

## Usage

```lean
import Compiler.SolidityImport.Import

solidity_profile build where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466   -- none = optimizer off
  bytecodeHash := "none"

solidity_import example from "Contracts/SolidityImportSmoke" entry "Slice.sol" using build
  contract C
  function f(Mkt, bytes32, address)
  function lossOf(bytes32)
```

- `from` is the Solidity project directory, relative to the importing
  package's `lakefile.lean`; its `remappings.txt` resolves imports. `entry` is
  the file declaring the contract.
- `solidity_profile` defines an ordinary `Profile` value (reusable,
  `#print`able). `using` takes any `Profile`, named or inline
  (`using { evmVersion := "osaka", ... }`). The settings go to solc and into the
  digest; they should match how the audited bytecode is built. `solc` defaults
  to the only accepted release, `0.8.34+commit.80d5c536`.
- Each `function` clause selects one root by name and Solidity parameter types.
  A struct may be qualified (`IMidnight.Market`). Roots are lowered
  independently and share one field list.

The command defines `example.model`, `example.report` (`toText` renders the
reviewed inventory), `example.sourceDigest`, and the kernel theorem
`example.covered`. It works inside namespaces.

Install the compiler once with `python3 scripts/setup_solc_import.py` (a
downstream package passes `--output .lake/solidity-import/solc-0.8.34`).
Elaboration never downloads a compiler; it checks the binary's SHA-256 before
and after running it.

Declare the Solidity tree as a Lake input so editing a source rebuilds the
import:

```lean
input_dir midnightSol where
  path := "vendor/midnight/src"
  filter := .extension "sol"
lean_lib MorphoMidnight where
  needs := #[midnightSol]
```

## Supported Solidity

This is deliberately the subset Midnight's `updatePositionView` needs, not a
claim to support arbitrary Solidity.

| Construct | Lowering |
| --- | --- |
| Explicit scalar/tuple return | `returnValues`, preserving order |
| Local declarations and storage aliases | Hygienic scalar bindings or resolved read paths |
| One/two-key mappings to structs | solc slots, word offsets, and packed uint offsets |
| Scalar member of a memory/calldata struct parameter | Explicit scalar projection; no ABI decoder |
| Unsigned `+`, `-`, `*`, `/` | Word arithmetic with overflow/underflow/zero-divisor panics |
| Unsigned comparisons, equality | Scalar conditions |
| Narrowing casts | Bit masks, not overflow checks |
| Ternaries | Lazy `ite` branches |
| Resolved acyclic helper calls | Inlined bodies with separate local scopes |
| Single assignment to a named assembly return | `xor`, `mul`, `lt`, as in `UtilsLib.min` |

Each root must return explicitly. Loops, state writes, external calls,
modifiers, recursion, virtual dispatch, named call arguments, signed
operations, and any other construct reached from a root are rejected with
`file:line:column`, the construct, the reason, and the call path from the root
(`closure: C.f -> L.unused`). Functions outside the closure are listed as
excluded and do not block the import. Only reached storage fields are decoded;
array/mapping struct members are reported as opaque and cannot be read.

## What each check establishes

Four questions are answered separately, per root; none implies the next.

1. **Importable.** The command succeeds, or fails with the diagnostic above.
   A partial model is never produced, so every listed root is importable.
2. **Runs on Denote** (`denoteCovered`). Every constructor in the body has an
   explicit denotation arm (not the catch-all). The kernel proof for all roots
   together is `x.covered`.
3. **Compiles** (`compilable`). The ordinary Verity compiler accepts the root on
   its own. This is a compile attempt, not a correctness result; agreement
   with Denote and solc is only sampled by the A/B/C campaigns below.
4. **Covered by compiler proofs** (`compilerProofCovered`). Always
   `unavailable`: the importer builds no `SupportedSpec` witness and
   `SupportedSpec` has no decision procedure. The report never implies it.

`x.report` records 1, 2 and 4 (`status` lines of `toText`). Compilation depends
on the compiler, not the import, so the differential driver reports all four:

```lean
#eval IO.print (Differential.statusText x.model x.report)
```

```text
function f
  importable true
  denoteCovered true
  compilable true
  compilerProofCovered unavailable (the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C)
```

## Trust boundary

solc's AST and storage layout, and the lowering in `Import.lean`, are trusted.
The model is built as ordinary values and quoted (`Quote.lean`); after
elaboration the definitions are evaluated back and must equal those values.
The digest is SHA-256 over framed JSON of the complete solc input, the selected
signatures, the solc release, and the sources of `Import.lean`,
`Coverage.lean`, `Report.lean`, `Quote.lean` and `Profile.lean`. Panic payloads,
gas, public ABI decoding and bytecode equivalence are outside the model.

Consumers should re-elaborate in CI, check the fresh model is `rfl`-equal to
the compiled import, and keep a reviewed inventory (`report.toText`) and a
golden `repr` of the model, as the pilot's `check_import.py` does.

## Differential validation

Tests supplement proofs; no test count establishes equivalence. Every case
runs three paths:

- **A:** the original Solidity, compiled by the pinned solc, run in Foundry.
- **B:** the imported model, run by `Denote.execStmtList` (the proofs'
  semantics) with Verity's pure Keccak for mapping slots.
- **C:** the model compiled by Verity to Yul, then by solc, run in Foundry.

A consumer supplies a JSON fixture (see
`Contracts/SolidityImportSmoke/differential.json`): source and signature,
input domains, argument projections, storage recipes and a fixed corpus.
Python builds calldata with `eth-abi` and storage slots with `eth-hash`,
independently of Verity. Unused packed bits, neighbouring words and unrelated
slots get noise. Each EVM case runs from a restored snapshot and must not
write storage.

A/B/C must agree on success/revert, return words and observed storage; A and C
must also agree on revert bytes. Timeouts, resource limits, unsupported
compilation and tool failures are harness errors, never reverts.

```sh
scripts/check_solidity_differential.sh --config Contracts/SolidityImportSmoke/differential.json \
  --output .lake/d/smoke --seed 2438 --cases 128        # inputs
scripts/check_solidity_differential.sh --programs 5 --cases 16 --seed 2438 \
  --output .lake/d/programs                             # generated programs
scripts/check_solidity_differential.sh --mutations --output .lake/d/mutants
scripts/check_solidity_differential.sh --replay --output .lake/d/smoke
scripts/check_solidity_differential.sh --reduce --reduce-seconds 120 --output .lake/d/failing
```

- **Generated programs** cover uint8/16/128/248/256 casts, checked arithmetic,
  ternaries and helpers. Each also runs renamed and helper-extracted variants
  that must behave identically (`metamorphic-divergence.json` on mismatch).
- **Replay and reduction.** A campaign records seeds, inputs, sources, solc
  input/output, Yul, bytecodes, tool versions and hashes. Replay refuses
  changed artifacts. The reducer shrinks inputs (and generated expression
  trees) while preserving the mismatch category.
- **Mutants** are real importer and Denote edits built in isolated copies.
  Each must produce a runtime divergence; one that fails to compile is
  invalid, not detected.
- **Importer regressions:** `python3 scripts/solidity_import_mutations.py`
  checks the golden model (`--update-golden` after review), hygiene,
  determinism, rejections with diagnostics, multi-root independence, and that
  source changes move the witness results and the digest.

CI runs fixed seeds on every PR (10 minutes) and longer input, program and
mutant campaigns nightly and on demand (60 minutes), archiving the evidence.
A timeout fails the job.

## Adding a construct

A new construct needs, in the same PR: positive, rejection, boundary and
interaction cases; an A/B/C fixture or generated-program coverage; a mutant
when it carries real risk; and the Lean proofs it enables. Keep the smoke
golden model and the Midnight proofs green, and turn every reduced
counterexample into a permanent regression.

EVMYulLean has a bytecode executor (`EvmYul.EVM.Ξ`) that could become a fourth
path; it would need account/block setup, opcode conformance checks and
independent result decoding, and must not replace Foundry.
