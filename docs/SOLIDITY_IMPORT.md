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
  to `0.8.34+commit.80d5c536`, and also accepts `0.8.10+commit.fc410830` for
  legacy London-era targets (`viaIR := false`, `evmVersion` up to `"london"`).
- Each `function` clause selects one root by name and Solidity parameter types.
  A struct may be qualified (`IMidnight.Market`). Roots are lowered
  independently and share one field list.

The command defines `example.model`, `example.report` (`toText` renders the
reviewed inventory), `example.sourceDigest`, and the kernel theorem
`example.covered`. It works inside namespaces.

It also defines typed accessors for specifications, with Solidity types
(`UIntN n`, `Uint256`, `Address`, `BytesN 32`, `Bool`):

- Function accessors are generated only when every parameter and return type
  has a scalar Lean representation. Tuple and array signatures do not receive
  these accessors; use the full model with the public Denote entry point and
  matching raw calldata for composite ABI execution. No synthetic
  `m_maturity` argument is generated.
- `example.position.credit oracle world id user : UIntN 128` reads
  `position[id][user].credit` with the imported layout (solc's slot, word
  offset and packing); `example.position.credit_val` states that its value is
  exactly the model's read. Key binders use the Solidity key names.

`oracle` computes mapping slots and is a parameter, so a theorem over these
accessors holds for any slot derivation; it does not identify slots with Keccak.

Install the compiler once with `python3 scripts/setup_solc_import.py --all` (a
downstream package passes `--output .lake/solidity-import/solc-0.8.34` or `--version 0.8.10 --output .lake/solidity-import/solc-0.8.10`).
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

## Proving properties of an imported function

State properties with the typed accessors above. The accessors unfold to
`runFunction` and `readMember` (`Compiler.SolidityImport.Access`), and
`evalExpr_structMember2_param` rewrites the model's own storage reads to
`readMember`. `Compiler.SolidityImport.Proofs` provides the lemmas used to
reason about the execution: word arithmetic (`sub_word`,
`mul_word128`, `div_word`, `mask_eq`), bindings (`lookup_bind_same`,
`lookup_bind_other`), and splitting a body into straight-line parts
(`split_prefix`, `list_frame`, `ends_return`). Solidity locals keep their name
in the model, so a proof can refer to `postSlashCredit` rather than to a
generated temporary. See
[morpho-midnight-verity](https://github.com/lfglabs-dev/morpho-midnight-verity)
for a complete example.

## Supported Solidity

The importer accepts the following constructs in a resolved function closure.
Other constructs fail with a located diagnostic; this is not general Solidity support.

| Construct | Lowering |
| --- | --- |
| Multiple selected entry points | One model with independently resolved root closures |
| `msg.sender`, `address(this)` | Dedicated caller and current-contract expressions, resolved by solc builtin declaration ids |
| `block.timestamp`, `block.number`, `block.chainid`, `tx.origin`, `address(this).balance` | Dedicated transaction- and account-context expressions (`Expr.blockTimestamp`, `Expr.blockNumber`, `Expr.chainid`, `Expr.txOrigin`, `Expr.selfBalance`), including `payable(address(this)).balance` and Yul `selfbalance()` / `origin()` |
| Ordinary nested root blocks | Ordered recursive lowering with unique local bindings, lexical lookup restoration, and propagated unconditional returns; unsupported nested control flow and statements after return reject with source locations |
| Explicit scalar/tuple return | `returnValues`, preserving order |
| Default scalar locals (development; validation pending) | Uninitialized unsigned integers, address, bool and bytes32 bind a fresh local to zero; reference and unsupported scalar defaults reject at the declaration |
| Scalar local writes (development; validation pending) | `=` and `delete` on materialized scalar locals; converted RHS evaluated before assignment; lexical shadowing retains declaration identity; compound writes and parameter writes reject |
| Invariant scalar `for` (development; validation pending) | uint256 counter from zero, strict `<`, increment by one; literal/parameter/unwritten-local bounds; body return/revert preserved; body counter writes, mutable bounds, break/continue reject |
| Schema ABI array-length `for` (development; validation pending) | Memory/calldata array length captured after its exact initial decoder; recursively checked body preserves memory headers; memory writes and external calls reject |
| Local declarations and storage aliases | Bindings named after the Solidity local (suffixed `_1`, `_2`, ... on collision), or resolved read paths |
| Scalar storage reads, `=`, and `delete` | Resolved uint8–uint256, address, bool, and bytes32 fields; exact solc slots and packed offsets; masked writes preserve neighboring bits and bool reads/writes normalize to 0/1 |
| Root fallthrough, bare `return;`, and named root return parameters | Void roots emit `stop` on fallthrough or bare `return;`; roots whose return parameters are all named scalars initialize each to zero, allow body reads/writes, and emit `returnValues` on bare `return;` or fallthrough; empty-body scalar hooks return zero words |
| One/two/three-key mappings to structs | solc slots, word offsets, and packed uint offsets (three-key mappings hash the outer two keys via `keccak256(abi.encode(k2, keccak256(abi.encode(k1, slot))))`) |
| One/two/three-key scalar mappings | address/uint256/bytes32/int256/bool/enum keys; uint8–uint256, int256, address, bytes32 and bool values; root assignment and `delete`, with masked narrow writes |
| Events | Resolved non-anonymous scalar events, including qualified library declarations, up to three indexed arguments and exact source-order data. Arguments must have total scalar preludes. Narrow unsigned event arguments require either a direct parameter of the declared type or an in-range canonical integer constant literal (`n < 2 ^ bits`); anonymous/dynamic events, named arguments and conflicting declarations reject with source locations. |
| Short-circuit boolean expressions and `!` | `&&` and `||` evaluate the left operand once; the right operand, including guards and helper preludes, executes only in its selected branch. Prefix `!` on a `bool` operand lowers to `Expr.logicalNot`. Unsupported constructs still reject even in unreachable operands. |
| `if` / `else` statements | Root statements lower to `Stmt.ite` on a boolean condition evaluated once; a branch `return` or `revert` stops execution and the continuation runs only on fallthrough. In inlined single-value helpers, the continuation after a returning branch is lowered once into the other branch and both results assign one fresh local; in inlined void and multi-return helpers, nested early `return` inside `if`/`else` lowers the post-conditional continuation into the fallthrough branch(es) after restoring branch-local lexical scope. Unsupported constructs still reject in unreachable branches. |
| Numeric literals and units (development) | Exact integral decimal/scientific/hex literals, including leading-dot fractions and digit separators, unsigned/bool named constants, and bounded sums of exact natural constant operands; seconds, minutes, hours, days, weeks, wei, gwei, ether. Fractional results, oversized words and general rational constant expressions reject. Focused checks pass 96 A/B/C transactions, 56 acceptance/rejection controls and 16 semantic mutants with minimal witnesses; the numeric parent `b0fa7b0e2` passed all 12 exact-head gates. |
| Exact natural constant products (development) | `int_const` multiplication of two lowered natural literals with empty preludes uses unbounded arithmetic and requires a uint256 result. Includes `100 * 365 days`; fractional operands, oversized intermediates and general rational operations reject. Focused checks at `bbc8fe0ad` pass 96 A/B/C transactions, 60 acceptance/rejection controls and a product mutant with a replayed minimal witness; full exact-head gates pending. |
| Inline constant array reads (development) | A directly indexed unsigned fixed array of exact natural constants lowers to a bounds guard (panic `0x32`) and value selection. Named constants are supported; nonconstant/guarded elements, other element types and escaping array values reject. Focused checks at `674cd89cd` pass 96 A/B/C transactions, 67 acceptance/rejection controls and three detected mutants with replayed minimal witnesses; full exact-head gates remain pending. |
| Unsigned modulo (development) | Typed unsigned `%` uses EVM remainder after a zero-divisor guard that panics with code `0x12`; narrow operands retain their declared unsigned width. Signed and general constant/rational modulo reject. Validation pending. |
| ABI array length (development, unvalidated) | Candidate `.length` lowering for schema-checked scalar or flat static-struct arrays inside memory/calldata struct parameters. Memory uses the materialized header; calldata checks the lazy header at source access. A/B/C fixtures, malformed inputs and two mutants are prepared; native validation and release gates remain pending. Storage arrays and other schemas remain unsupported. |
| Scalar ABI canonicality | Raw `uintN`, address and bool words are checked before source execution, including unused parameters. Noncanonical words revert with empty bytes. Complete-word A/B/C checks exercise mixed parameter positions; dynamic struct and partial-byte ABI validation remain outside this instrument. |
| Boolean literals | Resolved `true`/`false`; canonical 1/0 values |
| Flat static memory/calldata struct parameters | Full tuple ABI including unused scalar members; indexed field bindings and complete head sizes. Memory members are validated at entry; calldata members are validated when read, preserving competing reverts. |
| Dynamic memory/calldata structs (experimental) | Complete unsigned-scalar roots with dynamic scalar arrays or arrays of flat scalar structs. Full ABI signature, eager memory materialization and lazy calldata reads; direct element indices only. No legacy member projection. Mixed static/dynamic struct parameters and computed element indices reject precisely. Permanent fixtures cover pinned `Market` (340 A/B/C controls, four variants), scalar arrays (96 controls, three variants), and two dynamic roots (132 controls, four variants). Twenty dynamic ABI mutations are detected and minimized. Generated-name collision is checked against the actual decoder binding. Whole-library proof compatibility passes; exact-head campaign gates remain pending. |
| Unsigned `+`, `-`, `*`, `/` | Word arithmetic with overflow/underflow/zero-divisor panics |
| Unsigned comparisons, equality | Scalar conditions |
| `require(condition, "message")` | Exact `Error(string)` bytes; UTF-8 literals and resolved literal string constants, including empty messages, in roots and inlined helpers. The ABI payload extent must fit the EVM word address space; oversized messages reject at the source location. |
| `revert("message")` | Exact `Error(string)` payload through the same checked message lowering, including empty/UTF-8 literals and resolved literal string constants. Dynamic message expressions reject with source locations. New guard validation is under development; focused source admission/mutation campaigns remain pending. |
| `require(condition, CustomError(args))` and `revert CustomError(args)` | Resolved static unsigned/address/bool/bytes32 errors; arguments restricted to decimal numeric literals or scalar bindings; exact selector and ABI words (`revert CustomError(args)` lowers to `.requireError (.literal 0) name values`) |
| Narrowing casts | Bit masks, not overflow checks |
| Ternaries | Lazy `ite` branches |
| Resolved acyclic helper calls | Inlined single-value, void, and multi-return internal/private bodies with separate local scopes, including C3 virtual override resolution across `linearizedBaseContracts`, diamond `super.fn(...)` resolution, explicit base-qualified `Base.fn(...)` calls, and empty-body scalar virtual hooks |
| ABI encoding and Keccak (experimental) | `keccak256` over static scalar `abi.encode`, a single complete supported root struct, literal byte buffers and `abi.encodePacked` of unsigned/address/bool/bytes32 scalars and admitted byte buffers. Packed buffers preserve exact byte widths and lengths using aligned word memory; nested buffers receive separate allocations. Hex numeric literals retain their exact value. Dynamic byte parameters, arbitrary byte locals, direct packed structs, signed/fixed-byte widths other than bytes32 and effectful scalar arguments remain rejected. The focused 96-case A/B/C campaign includes unmodified pinned `IdLib.toId`, storage/events and rollback. All four generated variants agree, 15 semantic mutants are detected with minimized witnesses, and 11 located rejection/acceptance controls pass on captured local snapshots. Copy-loop and packed-allocation helper proofs use complete physical worlds in `AbiMemory`, `AbiPhysicalMemory` and `AbiPhysicalCopy`, with shared aligned-grid arithmetic in `AbiMemoryGrid`. The allocator establishes the coherence consumed by the byte-copy proofs; 79 public theorem audits use only standard axioms. The bounded full-tuple Smoke consumer and its five public theorem audits pass, as do four ABI consumer modules and their imported public proof audit. General byte-call integration and exact-head release gates remain pending. |
| Internal struct reference arguments | Root memory-to-memory and calldata-to-calldata references retain the exact ABI descriptor and nominal struct declaration identity across acyclic single-return helpers, including internal library receivers. External reference helper calls and raw Yul pointer access reject. Static and dynamic roots preserve eager memory/lazy calldata validation. Cross-location copies, storage references and unsupported reference expressions reject with source locations. Twenty A/B/C cases across four equivalent variants and a wrong-root mutation cover this rule; located rejection mutations cover external-call boundaries, location conversions and Yul name shadowing. |
| Single assignment to a named assembly return | `xor`, `mul`, `lt`, as in `UtilsLib.min` |

Non-empty roots with unnamed return parameters must return explicitly on every non-reverting path. Payable roots are rejected until value-transfer
semantics are supported. Other `msg`, `block`, and `tx` context members are
rejected when reached. Loops, mapping-to-struct writes, compound assignments, external calls,
modifiers, recursion, named call arguments, signed
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
`Coverage.lean`, `Report.lean`, `Quote.lean` and `Profile.lean`. The statement
denotation retains exact panic bytes; legacy scalar accessors erase failure
bytes. Gas, public ABI decoding and bytecode equivalence remain outside the
import certificate.

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

A/B/C must agree on success/revert, return words, observed storage, and exact
return/revert bytes. A payload-free Denote failure is a harness error. Timeouts, resource limits, unsupported
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
  The unchanged copy must first pass A/B/C on the same fixture and inputs;
  an existing divergence cannot count as a detected mutation.
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

Generated programs also exercise physical memory through the handwritten
`PhysicalCopySequence` and `CalldataWindowSequence` measuring fixtures. Each
has baseline, parameter-renamed and Yul-local-binding forms on the same
12-transaction sequence, with complete A/B/C observations compared between
forms. These fixtures retain explicit unchecked low-level obligations and do
not claim importer admission. The mandatory mutation inventory includes actual
Denote regressions that drop the copy or restore the incomplete selector-window
load; compilation failures do not count as semantic mutation detection.

EVMYulLean has a bytecode executor (`EvmYul.EVM.Ξ`) that could become a fourth
path; it would need account/block setup, opcode conformance checks and
independent result decoding, and must not replace Foundry.

## Pinned-corpus import coverage

`python3 scripts/solidity_import_coverage.py --fetch` checks the immutable
corpus in `scripts/solidity_import_corpus/manifest.json`: Midnight, Uniswap
v2/v3 core contracts, Pareto credit vaults, and OpenZeppelin ERC20/ERC4626.
`--fetch` permits downloading pinned source commits and checksum-verified
inventory compilers and dependency archives. No npm lifecycle scripts run.
Subsequent runs can omit it. Artifacts go to `.lake/solidity-import-coverage`;
CI publishes JSON, Markdown, per-function import logs, and the inventory
compiler input/output without making coverage a build gate.

The current denominator is **implemented functions in the selected
contract and its solc C3 inheritance chain**, including internal/private helpers.
Most-derived implementations win by signature; private helpers retain their
declaring-contract identity. Constructors, generated getters and abstract
declarations are excluded. Inherited implementation selection failures are
reported against the declaration that the importer cannot select. Each probe
checks the root's declaring contract in the import report, so a same-named
private helper cannot stand in for an inherited implementation.
Fallback/receive bodies remain counted and are rejected as unnamed roots.
Midnight is reported both in full and with only `multicall` removed for the
milestone. This is function-import coverage, not whole-contract ABI or EVM
coverage. Historical reports made before removal of scalar struct projections
may count projected imports; rerun the instrument on the current importer
before using those reports to assess complete ABI support.

Inventory uses the source project's pinned solc, preserving its original
pragmas. Each named declaration then goes through the actual Lean importer
under its current compiler pin. Source-version mismatches are reported as
pragma blockers, never fixed by rewriting sources. A successful probe requires
both a zero process status and the post-import marker. Timeouts, crashes,
unlocated importer errors, missing dependencies, and kernel errors are unknown
measurements. Unknown functions stay in the denominator; an unavailable
contract inventory suppresses the aggregate percentage. Reports explicitly
mark incomplete measurements and pending contracts. Fresh incomplete artifacts
replace prior-run output before the build starts; a timeout cannot leave an
old success report behind. The CLI returns nonzero for incomplete measurements,
which CI treats as advisory.

The first-blocker histogram weights each diagnostic by the number of rejected
functions encountering it first. These are **potential** unlocks, not a promise
that implementing that construct alone makes all those functions importable.
Rerun the report after each lowering family to reveal subsequent blockers.
The report records implementation hashes; source changes during measurement
invalidate that contract's results.
Legacy compiler-version blockers must be addressed before their construct
histograms can be compared with Midnight's. No coverage result is a proof of
semantic equivalence; that requires the separate differential/proof evidence.

The initial corpus campaign exposed uninitialized-local rejections that lacked
Solidity source locations. These remain unsupported, but now fail at the
`VariableDeclarationStatement` with a precise diagnostic instead of a missing
JSON-field error. This diagnostic correction does not change successful models
or the smoke golden; the importer source digest changes as designed.

### Imported transaction-context sequences

`EnvironmentSequence.sol` is an actual three-entry-point import.
`solidity_differential.check_environment` generates direct, local-binding, and
internal-helper variants in `programs.py`, imports each generated source into
Denote and the Verity compiler, and compares all three execution routes. It also
compares transaction inputs and complete observations between variants. Sender,
contract address, timestamp, block number, and chain id are checked through their
ABI return bytes across three funded callers. This fixture exercises context and dispatch; it does not
establish storage-write or external-call import support.

The executable context mutations replace each new imported context expression
with zero. Every mutant must first pass the unchanged fixture, then produce a
real A/B/C divergence and a separately replayed, deletion-minimal one-transaction
witness. Tool and compilation failures cannot count as detection.

### Imported scalar storage sequences

`StorageSequence.sol` imports three mutating entry points with packed uint128
siblings, a packed address/uint96 pair, and a full uint256 field. Transactions
exercise successive writes, deletion of one sibling while retaining the other,
and writes followed by a message-bearing revert. Direct, local-binding, and
reordered-write variants are independently imported and run through A/B/C.
Cross-variant comparison treats storage as a key/value map and touched slots as
a set; it preserves ordered events, status, and exact return/revert bytes and
rejects duplicated or missing storage observations.

The physical model fields are uint256 words with solc-derived bit ranges;
Solidity source types still control conversions and return ABI types. Boolean,
signed, array, and direct struct storage are rejected in this slice. Storage
assignments are accepted only as root statements. Helpers that write storage
are rejected until nested operand and argument evaluation order is validated. Mapping
writes and whole-contract deployment/initialization are not established by this
fixture. The importer still selects runtime function closures.

Write-aware executable coverage is separate from the original read-only
`stmtCovered` predicate and its world-preservation theorem. Storage frame lemmas
in `StorageFrames.lean` prove preservation of other persistent slots for the
actual Denote write helper and successful `setStorage` step, including packed
writes and normalized alias destinations. They do not by themselves prove a
whole-contract invariant or preservation of other bits in the same slot.

`EntryPointInvariants.lean` supplies `AllEntryPointsPreserve` obligations for
every public function in a model. Proving these obligations lifts an invariant
to arbitrary finite `EntryPointSequence`s. `ContextualEntryPointSequence`
additionally requires that environment preparation preserve the invariant.
The execution uses `Denote.effectiveFields`, including namespaced fields, and
the model's custom errors. Reverting frames restore the transaction's initial
world; `all_entry_points_preserve_of_success` therefore reduces the obligations
to successful calls and preservation by the frame reset.

`EntryPointInvariantChecks.lean` proves that a stored word stays at most one
across every sequence of three public entries: write zero, write one, and
write 99 followed by panic and rollback. This handwritten model illustrates
the proof interface; it does not establish an invariant for Midnight. ABI
decoding, dispatch, value transfer, and initialization remain separate
obligations, as do loop reasoning and external reentrant transitions.

`StorageVoidSequence` checks empty ABI responses and rollback from void entry
points. Its fallthrough lowers to `Stmt.stop`; the compiler's return-shape
validation remains unchanged. `StorageBytesSequence` separately checks bytes32
assignment, read, deletion, and rollback. Both have direct, binding, and
arithmetic-identity variants generated in `programs.py`.

### Imported scalar mapping sequences

`MappingSequence.sol` exercises one-key uint128 and bytes32 mappings, two-key
boolean authorization and uint128 consumption mappings, rollback, deletion,
and distinct transaction senders. Direct, local-binding and reordered-write
variants are imported independently and compared through the three stateful
routes. Mapping values are represented as a synthetic single member at word
zero, with solc-derived width; narrow writes retain the remaining word bits.
Boolean reads normalize the loaded byte to zero or one. No Solidity struct
member access is exposed by this internal representation.

Mapping slot observations evaluate keys in the current Denote state and use
the supplied Keccak oracle, including both hashes for nested mappings. Reached
key/value reads and writes before rollback remain observable. More than two
keys, signed/narrow/dynamic key types, unsupported value types, and compound
assignments remain rejected with source locations. Numeric literals with supported
denominations use the exact integral lowering described above; nonintegral
results and string literals used as numbers are rejected explicitly.

The mapping dirty-slot campaign seeds identical independently hashed slots in all
three routes. Its fixed prefix reads a noncanonical true byte, deletes it while
preserving upper bits, then reads the zero low byte with those upper bits still
set. Narrow assignments, deletes, rollback and later reads compare complete
words, including bits outside the declared value width.

Imported event sequence fixtures exercise indexed/unindexed scalar words,
empty and repeated events, and rollback of emitted events. The narrow fixture
uses a matching `uint128` parameter; widening a different parameter or passing
a local narrow value remains a located rejection under the compiler's existing
narrow event check. Generated renamed/binding/order variants preserve the exact
ordered event sequence. `--argument-bits` generates canonical narrow ABI words;
it does not claim malformed-calldata equivalence.

### Bounded-loop proof rule

`Compiler/SolidityImport/LoopInvariants.lean` proves an indexed-invariant rule
for Denote's actual `execForEachLoop`, and lifts it to `.forEach` after successful
count evaluation. The step obligation includes the normalized index binding;
the initial obligation includes the binding installed even when the bound is
zero. Normal completion establishes the invariant at the final index. Stop,
return, unclassified revert and byte-carrying revert have a separate explicit
postcondition, retaining their complete outcomes.

`LoopInvariantChecks.lean` applies the rule to a storage-writing loop for any
evaluated bound, and proves exact propagation of panic bytes on the first
iteration. This is model proof infrastructure: it adds no Solidity lowering
and does not establish a source-loop correspondence, gas bound, reentrancy
property or invariant of Midnight.

### Bounded symbolic execution

`Compiler/SolidityImport/SymbolicExecution.lean` composes already-established
Denote transitions. `denote_step using h` consumes one continuing statement;
`denote_prefix using h` composes an explicitly delimited prefix. Each uses the
provided equality proof and preserves the complete state. Neither tactic
unfolds expression evaluation or asks the kernel to reduce a whole imported
body. If the supplied theorem does not describe a matching continuing step,
the tactic fails rather than silently skipping it.

The terminal composition rule retains the entire outcome: final state for stop
or return, and exact byte list for a byte-carrying revert. The suffix is then
unreachable. These rules extend the generic list-composition lemmas ported
from the pinned Midnight pilot; they do not prove Solidity/model equivalence
or discharge the semantic obligations of an instruction. For loops, use the
indexed rule above to establish a bounded block theorem before composing it.

The check module exercises arbitrary-state step/prefix composition, early stop,
exact revert bytes, rejection of an incompatible step proof, and a concrete
bind-then-stop sequence whose unreachable suffix is arbitrary.

### Development slice: loops in inlined helpers

A shared loop lowering draft reuses the exact unsigned zero-start/unit-step/invariant-bound checks for root entry points and helpers. Helper loop bodies admit supported scalar locals, assignments/deletion, requires, events, conditionals and nested loops. A helper's final result resumes its caller; returns inside its loop body remain precisely rejected. `HelperLoopSequence` checks the caller continuation.

| Supported Solidity (development; native validation pending) | Lowering boundary |
| --- | --- |
| Invariant bounded `for` in an internal scalar-result helper | Shared counter/bound/header checks; helper body has no return; unsupported effects fail with source diagnostics |

No release validation or Midnight coverage improvement is claimed for this draft.

### Development slice: unsigned mapping-struct member writes

| Supported Solidity (development; native validation pending) | Lowering boundary |
| --- | --- |
| Assignment and `delete` of unsigned members in one/two-key mapping structs | Existing exact layout word offsets and packed masks; opaque/unsupported members reject; direct key preludes reject |
| Storage aliases with mutable local keys | Keys are captured into fresh bindings at declaration, including the outer key of a nested mapping |

`PackedMemberWriteSequence` exercises sibling fields, packed widths, full words, alias key changes, deletion, events and rollback. No native validation or Midnight coverage improvement is claimed yet.

### Development slice: internal helper expression effects

| Supported Solidity (development; native validation pending) | Lowering boundary |
| --- | --- |
| Scalar/local/mapping/unsigned mapping-struct assignments and `delete` in scalar-result helpers | Reuse the exact root effect rules and rejection diagnostics; execute effects before the helper continuation |

`HelperEffectSequence` checks writes, packed siblings, conditional effects, deletion, caller continuation and rollback. Compound operations, parameter writes, unsupported reference targets and external expression calls remain rejected. This draft has not passed native validation or full release gates.

The current revision also guards stateful helper calls inside ordinary binary operands and helper call arguments until their evaluation order is independently validated. Non-view declarations are conservatively classified as stateful. Short-circuit boolean branches retain their existing selected-branch evaluation; the fixture checks that a dead helper cannot write. These guards and the expanded fixture are development changes awaiting compilation and mutation controls.


### Development slice: fixed arrays behind mappings

| Supported Solidity (development; full release validation pending) | Lowering boundary |
| --- | --- |
| One-dimensional fixed unsigned arrays behind one/two-key mappings | Validate fixed length, unsigned base layout and exact rounded footprint; use floor(256/width) elements per slot and masked element writes/deletes |
| Dynamic unsigned indices into those arrays | Capture the index once, select the resolved element and emit exact panic 0x32 for an out-of-range index |
| Readonly storage-to-memory copies of those fixed arrays | Capture all elements at declaration; scoped descriptors preserve the snapshot across subsequent storage writes |

Effectful or reverting write keys, indices and RHS operands reject until their
evaluation order has dedicated validation. Dynamic/multidimensional/signed/bool
arrays, memory writes/aliases and whole-array values remain outside this slice.
Two preliminary 64-transaction A/B/C campaigns passed on recorded source hashes;
the second covered indices 0–8, snapshot identity, uint24 cross-word packing,
delete, two mapping keys and rollback. New exact-head variants, rejection and
mutation controls and full release gates are still pending.

The fixed mapping-array key/index order audit passed 32 actual A/B/C transactions
on `2a448958`: two state-changing helpers produced stamp12 on success, invalid
indices produced panic0x32, and competing helper failures produced the exact
`first array key` revert bytes. This establishes that fixture under the pinned
compiler settings; it is not a general Solidity evaluation-order theorem.


### Development slice: fixed-array assignment evaluation order

| Supported Solidity | Exact lowering |
| --- | --- |
| Checked/effectful RHS and key/index expressions of mapped fixed-array assignments | Evaluate and capture the RHS, then the mapping keys and index in recursive source order, then bounds-check and perform the masked write. Existing expression rejection boundaries remain in force. |

The pinned solc 0.8.34 via-IR/Osaka/466-runs A-only audit at `3bc74c208`
observed the stamp `312` for RHS/key/index helpers and RHS error priority over
bounds and key errors. This is evidence for that fixture/profile, not a general
Solidity evaluation-order theorem. `FixedArrayWriteOrderSequence` extends the
A/B/C obligations to distinct key/index/RHS failures, checked division and
narrowing, emitted events, bounds and rollback; baseline, identifier-renamed
and explicitly captured-RHS variants must have identical observations. Two
runtime mutations exchange RHS/LHS order or corrupt the captured RHS. These
new A/B/C campaigns and full exact-head gates are **pending**; no additional
Midnight importability is claimed yet. The prior three key/index/RHS rejection
controls become positive controls for the newly admitted forms; compound and
dynamic writes and unresolved stateful binary-operand order remain rejected.


### Development slice: discarded scalar helper calls

| Supported Solidity (development; native validation pending) | Lowering boundary |
| --- | --- |
| Internal/private scalar-result helper calls used as expression statements, including library calls | Keep the helper prelude, materialize the final result even when unused, then resume the caller; retain recursion, dispatch, argument-order and reference-conversion guards |

The fixture checks helper storage writes, events, early return, caller continuation,
library reverts and rollback. Void/multiple-result helpers and calls to external
or public declarations remain precisely rejected in this statement slice. This
prerequisite does not implement `IdLib.storeInCode`: named returns, dynamic byte
construction and CREATE2 still require independent exact lowering and observations.
Generated variants and an effect-drop runtime mutant are registered; native and
full release checks remain pending. Existing Denote instructions are reused.

Helper-result continuations also reuse the exact root `emit` lowering, keeping events
before the continuation and rollback intact. The fixture retains helper events;
a separate event-drop runtime mutation and anonymous/dynamic event rejection
controls are registered. Native validation remains pending.

### Development slice: encoded byte locals

| Supported Solidity (development; complete validation pending) | Lowering boundary |
| --- | --- |
| Initialized `bytes memory` locals from admitted ABI/packed encodings or literals; local aliases | Evaluate encoding once at declaration and retain a payload pointer and logical length. Hashing and packed concatenation consume those captured descriptors; branch/helper/root scope restoration preserves declaration identity. |

The initial draft fixture passes 64 real A/B/C transactions with repeated reads,
aliases, nested buffers, branch locals, storage/events and rollback. Generated
variants, three runtime mutations and nine located controls are added but await
native validation on the final commit. Byte assignment/index writes, length
access, `new bytes`, byte parameters/helper reference calls, raw Yul pointers and
deployment remain unsupported and rejected. The descriptor is a payload view,
not a claim of general Solidity byte-object memory layout. Full exact-head release
gates remain pending.

### Development slice: named scalar helper results

| Supported Solidity (development; native validation pending) | Lowering boundary |
| --- | --- |
| Named unsigned/address/bool/bytes32 result in a single-result internal helper | Initialize a declaration-bound result to zero, preserve assignments and early explicit returns, and return its value on fallthrough. Restore result context across nested helper calls. |
| Existing single Yul assignment followed by a helper continuation | Assign the named result only when `InlineAssembly.externalReferences` resolves the target identifier to the active helper return declaration (`!isOffset`, `!isSlot`, no suffix, `valueSize == 1`), then continue with the following statements. Clean narrow unsigned/address results by masking and booleans by nonzero normalization. Assembly assignments in branches retain the caller continuation. |

A structural direct-result path retains existing full-word single-terminal-assembly
models. This adds no Yul builtin, deployment or external-call semantics. Yul reads
of narrow named results are rejected because the current result slot stores a
clean Solidity value, whereas Yul could observe dirty bits. Shadowed local
targets with the same name as the helper return reject at the Yul assignment;
reference locals (`bytes memory`, fixed memory array snapshots and storage
aliases) erase shadowed names from Yul identifier lookup within their lexical
scope. Reference/tuple results, modifiers, recursive calls and statements after
an explicit return remain rejected. Bare returns are rejected, matching the
pinned solc source audit; implicit named-result fallthrough is supported.

The initial draft passed 93 build jobs and 64 A/B/C transactions. The expanded
fixture adds nested contexts, boolean/address cleanup, assembly branch
continuation and lexical shadowing. Three generated variants, runtime and guard
mutants and sixteen located controls await native validation on the final commit.
Full release gates and the pinned pilot check remain pending; no golden or
provenance was changed.

### Development slice: numeric Yul expressions

| Solidity construct | Lowering |
| --- | --- |
| Untyped decimal or hexadecimal Yul numeric literal fitting one EVM word | Parse the exact natural value and reject values outside `[0, 2^256)`. |
| Two-argument Yul `add` in the existing single-assignment helper subset | Use the existing wrapping word addition expression. |

This draft reuses existing literal and addition semantics in Denote and codegen.
It does not expose byte-buffer pointers or add raw memory, deployment, additional
assembly statements, typed literals or nonnumeric literals. These remain precise
rejections. `YulNumericSequence` exercises decimal, hex and full-word literals,
overflow, storage, events and rollback. Baseline, identifier-renamed and numeric
normalization/commuted-add variants are generated; runtime literal/add mutations
and located acceptance/rejection controls are registered. Native validation,
exact-head release gates and the pinned pilot check are pending. This is a
prerequisite for the measured IdLib path, not an implementation of `storeInCode`.

### Development slice: pinned `solc 0.8.10` release and single-quoted imports

| Supported profile / source form | Lowering and provenance boundary |
| --- | --- |
| `Profile.solc := "0.8.10+commit.fc410830"` | Verified against `.lake/solidity-import/solc-0.8.10` SHA-256 pins (Linux and macOS) before and after invocation; requires `viaIR := false` and `evmVersion` up to `"london"`. |
| Single-quoted and double-quoted `import` paths | `importSpecs` extracts both `'...'` and `"..."` import specifiers; after compilation, every key in `parsed["sources"]` must belong to the explicitly collected `sources` map so `solc 0.8.10` cannot silently load uncollected host files without `--no-import-callback`. |

### Development slice: C3 inheritance, virtual helper dispatch, and `super` / base-qualified calls

| Supported Solidity | Lowering boundary |
| --- | --- |
| Inherited root entry points across `linearizedBaseContracts` | `selectFunction` walks the target contract's C3 `linearizedBaseContracts` in most-derived-first order, preferring implemented declarations over unimplemented interface/abstract declarations in the same virtual override family (`baseFunctions` transitive closure) or parameter signature, and switches `currentFile` to the declaring file of the selected root. |
| Unqualified internal/private helper calls in base contracts | When the referenced function's enclosing contract belongs to the target contract's `linearizedBaseContracts`, `lowerCall` resolves the call to the first implemented override in the target contract's C3 chain sharing the same transitive `baseFunctions` family, and restores `currentFile` across inlined helper frames. |
| `super.fn(...)` helper calls | Verified against `referencedDeclaration == -25` (`type(contract super ...)`); resolved to the first implemented function in the same transitive `baseFunctions` family across the suffix of the target contract's `linearizedBaseContracts` strictly after the calling function's enclosing contract (matching `solc` C3 diamond `super` dispatch). |
| Explicit base-qualified `Base.fn(...)` helper calls | Verified that `Base` is an identifier in the target contract's `linearizedBaseContracts` and that `fn` is declared in `Base`, then inlined statically without virtual dispatch. |
| Duplicate `storageLayout` labels (e.g. OpenZeppelin `private __gap`) | Unreferenced duplicate labels in `storageLayout.storage` do not block importing supported functions; any reference to a state variable whose label appears multiple times in `storageLayout.storage` fails closed with `shadowed storage declaration <name> is outside this slice`. |

### Development slice: void helpers, custom-error reverts, scalar booleans, and named root returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Zero-return internal, private, and internally-called public helpers | Lowered via continuation-passing (`lowerVoidHelperFrom`) so nested early `return;` inside `if`/`else` runs the post-conditional continuation only on fallthrough paths with restored lexical scope. |
| `revert CustomError(...)` (`RevertStatement`) | Lowered through `lowerErrorArguments` to `Stmt.requireError (.literal 0) name values`. |
| Scalar `bool` storage variables and prefix `!` | Stored as 8-bit packed storage with `logicalNot (logicalNot ...)` normalization on read and write; prefix `!` on `bool` lowers to `Expr.logicalNot`. |
| Named scalar root return parameters and empty-body scalar hooks | Root functions whose return parameters are all named scalars initialize each to zero and return them on bare `return;` or fallthrough; empty-body root or helper hooks return zero words. |

### Development slice: pre-placeholder modifiers, `unchecked` blocks, compound assignments, and scalar assignment expressions

| Supported Solidity | Lowering boundary |
| --- | --- |
| Pre-placeholder modifiers (`ModifierDefinition` / `ModifierInvocation`) | Modifiers whose body ends with a single trailing `_;` (`PlaceholderStatement`) and contains no earlier `_;`, no `return;`, and no `virtual` specifier are inlined in declaration order before root and helper bodies with their own lexical frame and `unchecked := false`. |
| `unchecked { ... }` (`UncheckedBlock`) | Enables wrapping unsigned arithmetic (`+`, `-`, `*` masked to `2 ^ bits - 1` when `bits < 256`) within the lexical block while preserving division/modulo-by-zero panic (`0x12`) and resetting `unchecked := false` across helper and modifier call boundaries. |
| Compound assignments (`+=`, `-=`) | Supported on declaration-bound unsigned scalar locals, unsigned scalar storage fields, unsigned scalar mappings, and unsigned mapping struct members, honoring checked vs `unchecked` arithmetic. |
| Scalar assignment expressions (`(x = rhs)`) and constant `**` | Supported for `=` on declaration-bound scalar locals and scalar storage identifiers when any binary sibling operand is order-independent (`Literal` or constant) and call sites are single-argument; integer constant `a ** b` lowers when `a ^ b < 2 ^ 256`. |

### Development slice: multi-return helper inlining, tuple destructuring, parameter compound assignments, and narrow constant event arguments

| Supported Solidity | Lowering boundary |
| --- | --- |
| Multi-return internal, private, and internally-called public helpers | Unnamed multi-return scalar helpers (`returnParameters.parameters.size > 1`) allocate fresh `letVar` result bindings initialized to zero, evaluate and convert `Return` tuple components in source order into those bindings, and thread post-`if`/`else` continuations along fallthrough paths via `lowerVoidHelperFrom`. Named or reference return parameters and discarded multi-return calls remain rejected. |
| Tuple destructuring declarations and assignments (`(uint256 a, uint128 b) = fn(...)`, `(a, b) = fn(...)`) | Supported when the RHS is a multi-return helper call of matching arity; `VariableDeclarationStatement` requires at least one non-null declaration and binds declared components in order; `Assignment` (`=`) evaluates converted components into fresh temporaries and commits each non-elided target to a materialized scalar local or scalar storage field in order after rejecting duplicate local or storage targets. |
| Compound assignments (`+=`, `-=`) on unsigned scalar parameters | When an unsigned scalar parameter is modified by `+=` or `-=` in a root, helper, or modifier body (without direct `=` or `delete` parameter writes), the parameter is materialized into a declaration-bound mutable local copy at frame entry so call-by-value updates are visible within the frame without mutating caller bindings. |
| Narrow constant event arguments (e.g. `emit Initialized(type(uint8).max)`) | Canonical integer literals `Expr.literal n` with `n < 2 ^ bits` and empty prelude are accepted for `.uintN bits` event parameters in both `Import.lean` and `ValidationEvents.lean`, alongside direct matching `.uintN bits` parameters. |

### Development slice: `int256` arithmetic/storage/mappings and contract-typed scalar values

| Supported Solidity | Lowering boundary |
| --- | --- |
| `int256` / `int` scalar parameters, locals, returns, scalar storage fields, and scalar mapping values | Lowered as full 256-bit two's-complement words (`ParamType.int256` and `Word Int256` accessor bridge); narrow signed types (`int8`..`int248`) and signed mapping keys remain rejected. |
| `int256` prefix unary `-`, binary `+`, `-`, `*`, `/`, `<`, `>`, `<=`, `>=`, `==`, `!=`, and `+=` / `-=` | Checked `+`, `-`, `*`, `/`, and unary `-` emit `Panic(0x11)` on two's-complement `int256` overflow (including `-type(int256).min`, `type(int256).min * -1`, and `type(int256).min / -1`) and `Panic(0x12)` on division by zero; `UncheckedBlock` switches signed `+`, `-`, `*`, `/`, `+=`, `-=`, and unary `-` to wrapping 256-bit two's-complement arithmetic while preserving division-by-zero `Panic(0x12)`. Signed comparisons use `slt` / `sgt` and signed division uses `sdiv`. |
| `type(int256).max`, `type(int256).min`, `type(uintN).min`, and `int256(x)` / `uint256(int256_x)` casts | `type(int256).max` lowers to `2^255 - 1`, `type(int256).min` to `2^255` (`-2^255` in two's complement), and `type(uintN).min` to `0`; explicit `int256(...)` and `uint256(...)` casts on 256-bit scalars and bounded constants preserve the 256-bit word representation. |
| Contract and interface scalar values (`contract Foo`, `address payable`) | Supported as 160-bit address-backed scalar parameters, locals, returns, scalar storage fields, scalar mapping values, and `ContractOrInterface(addr)` / `address(contractVal)` casts; external contract member calls fail closed with located diagnostics. |

### Development slice: internal function-pointer locals, mapping-struct `delete`, and post-placeholder modifiers

| Supported Solidity | Lowering boundary |
| --- | --- |
| Internal function-pointer local declarations (`function(...) internal ... ptr = f` or `cond ? f : g`) | Supported when initialized at declaration time to a direct internal/private helper identifier or a `Conditional` (`cond ? f : g`) whose branches resolve to internal/private helpers in the active contract hierarchy. For a conditional initializer, the condition is evaluated once at declaration and stored in a fresh boolean local; calling `ptr(args)` lowers to `lowerCall` on a direct target or a conditional dispatch evaluating arguments once in caller source order and branching on the stored condition to inline each target helper. Reassignment, uninitialized function-pointer locals, function-pointer parameters/returns/storage, and external function pointers fail closed with located diagnostics. |
| Whole-struct `delete` on mapping-backed structs (`delete m[k]`, `delete m[k1][k2]`) | Supported when the referenced struct has no `opaque` (nested mapping or dynamic array) members in `storageLayout` and every decoded member is an unpacked or packed scalar (`uint8`–`uint256`, `int256`, `address`, `bool`, `bytes32`). Keys are evaluated once into fresh temporaries if needed and each member is cleared to `0` in layout order. Structs with `opaque` or array members fail closed. |
| Modifiers with statements after `_;` (`ModifierDefinition` / `ModifierInvocation`) | Modifiers with a single top-level `_;` (`PlaceholderStatement`) may include both pre-placeholder and post-placeholder statements (for example `nonReentrant` guards). Multiple modifiers wrap outside-in around the body (`m1` outer, `m2` inner). On every non-reverting return or fallthrough path, return values are captured into fresh temporaries before running post-placeholder statements in the modifier's lexical frame. Modifiers with zero, multiple, or nested `_;` placeholders, `virtual` modifiers, and `return;` inside a modifier body fail closed. |

### Development slice: empty-body dynamic array returns and root `bytes calldata` parameters

| Supported Solidity | Lowering boundary |
| --- | --- |
| Empty-body root functions returning a single dynamic array (`T[] memory`, named or unnamed) | Supported when `T` is a canonical return array element (`uint256`, `int256`, `address`, `bool`, `bytes32`), the function body has no statements, and the function has no modifiers. Lowers to `Stmt.returnValues [.literal 32, .literal 0]` with `returns := [.array elemTy]` (the 64-byte ABI encoding of an empty dynamic array: offset `0x20`, length `0x00`). Non-empty bodies, modifier-wrapped bodies, or non-canonical element widths returning `T[] memory` fail closed. |
| Root `bytes calldata` parameters (named or unnamed) and `.length` | Supported with `abiDecoding := .explicitPrelude` via `AbiLowering.bytesCalldataHead`, which enforces `solc`'s exact entry checks (`calldatasize >= 4 + 32 * rootHeadWords`, `relOffset <= 2^64 - 1`, `header + 31 <s calldatasize`, `length <= 2^64 - 1`, and `dataOffset + length <= calldatasize`). Unnamed root parameters receive a hygienic identifier so `Param` validation succeeds while preserving the canonical ABI signature. `.length` lowers to the validated `lengthBinding` local; `bytes memory` root parameters, `bytes` locals, and value uses of `bytes calldata` fail closed. |

### Development slice: same-contract overloaded helpers, constant custom-error arguments, conditional tuple expressions, and Yul `tload`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Same-contract overloaded function declarations (`overloadedDeclarations` in `refInt`) | When `solc` records non-empty `overloadedDeclarations` on a function reference, `refInt` accepts the resolved `referencedDeclaration` if every candidate in `overloadedDeclarations` either belongs to the same virtual override family (`sameVirtualFamily`) or shares an origin declaring contract across `baseFunctionClosure` (for example `ERC20._approve(3)` and `ERC20._approve(4)` declared in the same contract). Cross-contract overloads with distinct signatures and no override relationship remain rejected (`ambiguous declaration`), and importing two overloaded roots with the same name in a single slice fails closed (`root function name collision`). |
| Compile-time constant scalar expressions in custom-error arguments (`address(0)`, `type(uintN).max`, named constants) | Alongside decimal literals and direct scalar bindings, `lowerErrorArguments` accepts pure scalar expressions (`numericConstants` identifiers, `typeConversion` casts such as `address(0)`, and `type(T).max`/`min`) whose lowered value has an empty statement prelude (`converted.pre.isEmpty`) and a canonical literal `Expr.literal n` satisfying `Denote.errorScalarValueValid modelType n`. Non-constant or effectful expressions fail closed. |
| Conditional tuple expressions (`cond ? (a0, ..., ak) : (b0, ..., bk)`) | Supported as the RHS of tuple variable declarations (`lowerLocal`) and tuple assignments (`lowerEffect`), including nested `Conditional` branches whose leaves are `TupleExpression`s or multi-return helper calls of matching arity. Target component types are threaded into each leaf so integer constants (such as `0 days`, `1 days`) convert to the declared component type before branch joining via fresh temporaries and `Stmt.ite`. Stateful or assignment expressions inside tuple components and bare top-level `TupleExpression` RHSs fail closed. |
| Transient storage `tload(slot)` in single-assignment `InlineAssembly` | `lowerYul` lowers `tload(a)` to `Expr.tload`, covered by `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses` (evaluating `DenoteState.transientStorage`). `tstore` and multi-statement assembly blocks remain outside this slice. |

### Development slice: fixed-size unsigned scalar array members in mapping structs and root fixed-size array returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Fixed-size unsigned scalar array members inside mapping structs (`struct S { ... uintN[L] arr; }`) | Decoded from `storageLayout` when the array member has `encoding == "inplace"`, `byteOffset == 0`, positive length `L`, and unsigned scalar elements (`uint8`–`uint256`). Expanded on demand (`usedStructFixedArrays`) into packed or full-word `StructMember` entries `__solidity_struct_array_{member}_{index}` at `wordOffset + index / perWord` only in slices that access the array member; unreferenced array members remain listed in `report.opaqueMembers`. Element reads, writes, `delete`, and memory snapshot copies (`uintN[L] memory snap = m[k].arr;`) enforce dynamic bounds checks (`Panic(0x32)`). Whole-struct `delete m[k]` and whole-array `delete m[k].arr` fail closed. |
| Unnamed root fixed-size scalar array returns (`returns (T[L] memory)`) | Supported when a root function declares a single unnamed `T[L] memory` return parameter with supported scalar element type `T` and positive length `L`. Lowered as `L` consecutive ABI return words (`Array.replicate L elemPty`); `Return` statements accept either an inline array literal `[e_0, ..., e_{L-1}]` (converting each pure/stateless component to `T` in order) or a local fixed-size array snapshot identifier of matching type and length. Named `T[L] memory` return parameters, stateful inline array components, and non-snapshot return expressions fail closed. |

### Development slice: `msg.data` / `_msgData()` support and `enum` scalar types

| Supported Solidity | Lowering boundary |
| --- | --- |
| `msg.data.length` and `_msgData().length` | `msg.data` is verified against `referencedDeclaration == -15` and `t_magic_message`; `.length` on `msg.data` or on a zero-argument internal/private/public helper returning `msg.data` (or forwarding another such helper) lowers to `Expr.calldatasize` after running any modifier prelude/postlude on the inlined helper. Multi-statement or parameterized `bytes` helpers fail closed. |
| Zero-parameter root functions returning `msg.data` or `_msgData()` (`returns (bytes memory)` / `returns (bytes calldata)`) | Supported when the root function takes zero parameters and declares a single unnamed `bytes memory` or `bytes calldata` return parameter (`rootMsgDataReturn`). `return msg.data;` or `return _msgData();` lowers to `Stmt.returnValues [.literal 32, .calldatasize, .calldataload (.literal 0)]` with `returns := [.bytes]`, emitting the exact 96-byte ABI encoding of the 4-byte selector calldata (`offset = 32`, `length = calldatasize`, `word0 = calldataload(0)`). Parameterized roots or arbitrary `bytes` return expressions fail closed. |
| `enum` declarations, `Enum.Member`, `type(Enum).min` / `type(Enum).max`, and `Enum` parameters/locals/returns/events/errors | `EnumDefinition`s with `1..256` members are indexed by declaration ID and qualified type name (`enum Contract.Name` / `enum Name`) and lowered as `.uintN 8` scalars. `Enum.Member` lowers to its zero-based ordinal literal, `type(Enum).min` to `0`, and `type(Enum).max` to `members.size - 1`. Root `Enum` parameters emit an entry calldata guard `calldataload(offset) < members.size` that reverts with empty data on out-of-range ordinals (matching `solc` ABI decoding). Uninitialized `Enum` locals default to `0` (first member). Events and custom errors accept `Enum` parameters as `.uintN 8`, including constant `Enum.Member` arguments. |
| Explicit `Enum(x)` and `uintN(enumVal)` casts | `uintN(enumVal)` is a no-op on the underlying 8-bit ordinal; `Enum(x)` from an unsigned integer, `int256`, or integer constant evaluates `x` once and emits a runtime bounds guard (`x < members.size`) that panics with `Panic(0x21)` on out-of-range values. Fallible `Enum(x)` conversions inside `abi.encode` / `abi.encodePacked` arguments and `enum` struct members or storage fields fail closed. |

### Development slice: unsigned exponentiation, bitwise/shift operators, extended compound assignments, and Yul arithmetic/bitwise builtins

| Supported Solidity | Lowering boundary |
| --- | --- |
| Unsigned exponentiation (`**`) in checked and `unchecked` blocks | In `unchecked` blocks, `a ** b` on `uintN` lowers to `Expr.externalCall "exp" [a, b]` (masked to `2^bits - 1` when `bits < 256`). In checked mode, `a ** b` is supported when either the base or the exponent is a canonical integer literal with an empty prelude: a constant base `B >= 2` checks `b <= maxSafeExponent(B, bits)` (`B^maxExp < 2^bits`) and emits `Panic(0x11)` on overflow; a constant exponent `E >= 2` checks `a <= maxSafeBase(E, bits)` (`maxBase^E < 2^bits`) and emits `Panic(0x11)` on overflow; `0 ** b` lowers to `b == 0 ? 1 : 0` and `1 ** b` / `a ** 0` lower to `1` after evaluating the dynamic operand once. Checked exponentiation with both base and exponent dynamic fails closed. |
| Bit shifts (`<<`, `>>`), bitwise binary operators (`&`, `|`, `^`), and unary bitwise negation (`~`) | Constant `int_const` shifts (`a << b`, `a >> b`) fold when non-negative and `< 2^256`. Runtime `a << b` and `a >> b` require an unsigned shift amount `b` and lower to `Expr.shl b a` (masked to `2^bits - 1` for narrow `uintN`), `Expr.shr b a` (unsigned `uintN`), or `Expr.sar b a` (`int256` arithmetic right shift), matching Yul's `(shift, value)` argument order. Binary `&`, `|`, `^` and unary `~` support `uintN`, `int256`, and `bytes32`, masking `~x` to `2^bits - 1` for narrow `uintN`. |
| Extended compound assignments (`<<=`, `>>=`, `&=`, `|=`, `^=`, `/=`, `%=`) | Supported across declaration-bound scalar locals, writable helper/modifier parameters (`bodyCompoundAssignedIds`), scalar storage fields, scalar mappings, and unsigned mapping-struct members: `<<=`, `>>=`, `&=`, `|=`, `^=`, `/=`, `%=` on `uintN`; `/=`, `<<=`, `>>=`, `&=`, `|=`, `^=` on `int256`; and `&=`, `|=`, `^=` on `bytes32`. `*=` and signed `%=` remain rejected. |
| Single-assignment Yul arithmetic, comparison, and bitwise builtins (`sub`, `div`, `mod`, `and`, `or`, `shl`, `shr`, `sar`, `gt`, `eq`, `iszero`, `not`) | Extended `lowerYul` in the single-assignment inline assembly subset (such as `UtilsLib.zeroFloorSub`), lowering directly to the corresponding `Expr` constructors covered by `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses`. |

### Development slice: bounded `while` loops, Yul `clz`, struct local declarations, and `calldata`-to-`memory` struct conversions

| Supported Solidity | Lowering boundary |
| --- | --- |
| Bounded unsigned `while` loops (`WhileStatement`) and `--counter` / `counter -= 1` in `for` loop headers | `lowerWhile` supports `while (v != 0)` / `while (v > 0)` (and `0 != v` / `0 < v`) on a writable unsigned `uintN` local `v` (`bits ≤ 256`) when the body contains no `return`, does not assign `v` before the final statement, and ends with a strictly decreasing bit-clearing or right-shift update: (1) positive constant right shift (`v >>= k` or `v = v >> k`, `1 <= k < 256`), (2) lowest-set-bit clear (`v &= v - 1` or `v = v & (v - 1)`), or (3) MSB bit clear (`uintM b = msb(v); ...; v &= ~(1 << b)` or `v = v.clearBit(b)` where `msb` computes `sub(255, clz(x))` and `b` is not reassigned). Lowered to `Stmt.forEach loopVar (.literal bits) [.ite condVal.expr bodyOut.toList []]`, which executes at most `bits` guarded iterations. `lowerFor` also accepts `--i` and `i -= 1` as `for` loop step expressions so `bodyAssignedIds` detects any counter mutation in loop bodies. |
| Yul `clz(x)` in single-assignment `InlineAssembly` | `lowerYul` lowers `clz(a)` (EIP-7939 Count Leading Zeros, 256 for `0`) into an unrolled 8-step binary search over `[128, 64, 32, 16, 8, 4, 2, 1]` using `Expr.shr` and `Stmt.ite`, producing a pure `Denote`- and `Yul`-compatible statement prelude without requiring custom EVM opcodes in downstream proofs. |
| `memory` and `calldata` struct local declarations (`Struct memory s = ...`, `Struct calldata s = ...`) and `calldata`-to-`memory` helper argument conversions | `lowerLocal` supports non-reassigned `memory` and `calldata` struct locals initialized from a root/helper struct reference (`.mem`) or a struct-array element (`m.tranches[i]`, `.abiElement`). Initializing a `memory` struct local or `memory` helper parameter from a `calldata` struct or `calldata` struct-array element materializes the struct into freshly allocated memory (`AbiRootLowering.materializeFromCalldata` / `AbiRootLowering.materializeElementFromCalldata`), validating scalar bounds and array heads at copy time; `memory`-to-`calldata` conversions and reassigned struct locals fail closed with located diagnostics. Referenced `immutable` state variables fail closed with `immutable state variable <name> is outside this slice`. |

### Development slice: `abi.encodeWithSelector`, `.selector` byte buffers, Yul arithmetic/bitwise/context builtins, and external/ABI rejection diagnostics

| Supported Solidity | Lowering boundary |
| --- | --- |
| `<typeOrLocalOrThis>.<fn>.selector` in `abi.encodeWithSelector` and `abi.encodePacked` | `lowerSelectorBytes` resolves the referenced function or public state-variable getter declaration's 8-character `"functionSelector"` hex string and allocates a 4-byte memory buffer containing the left-aligned 32-bit selector word (`word * 16^56`, `size := 4`). `isPureSelectorReceiver` requires the receiver to be a contract/interface/library type (`type(contract ...)`), `this`, a literal, or a local/parameter variable (including `Contract(x)` casts around them); storage-variable receivers fail closed (`selector receiver must be a contract/interface type, this, or a local/parameter`) because unoptimized vs via-IR optimized `solc` differ on whether evaluating `stateVar.fn.selector` emits an `SLOAD`. Standalone `.selector` expressions outside `abi.encodeWithSelector` / `abi.encodePacked` fail closed. |
| `abi.encodeWithSelector(selector, args...)` as an encoded byte buffer (`keccak256(...)`, `bytes memory` locals, `abi.encodePacked(...)`) | Lowered by `lowerEncodedBytes`: for zero payload arguments, returns the 4-byte `lowerSelectorBytes` buffer directly; for one or more scalar arguments, validates and lowers each argument in order (`checkEncodingScalar`), stores their 32-byte words via `AbiEncoding.staticWords`, and concatenates the 4-byte selector prefix and `32 * n`-byte argument payload into a freshly allocated `(4 + 32 * n)`-byte buffer via `AbiEncoding.packedBuffer` and `AbiEncoding.copyBytes`. Non-byte-buffer uses of `abi.encodeWithSelector` fail closed with `abi.encodeWithSelector is only supported as a byte buffer`. |
| Extended Yul arithmetic, bitwise, comparison, and context builtins (`sdiv`, `smod`, `exp`, `byte`, `signextend`, `slt`, `sgt`, `caller`, `address`, `timestamp`, `number`, `chainid`) | `lowerYul` validates builtin name and arity before lowering arguments (`unsupported Yul builtin <fname>`), and lowers `sdiv`, `smod`, `byte`, `signextend`, `slt`, `sgt`, `caller`, `address`, `timestamp`, `number`, and `chainid` to their exact `Expr` counterparts (and `exp(a, b)` to `Expr.externalCall "exp" [a, b]`). `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses` include `.smod`, `.byte`, and `.signextend` with reflexive `rfl` arm-pin lemmas `evalExpr_smod_arm`, `evalExpr_byte_arm`, and `evalExpr_signextend_arm`. |
| Located diagnostics for `<addr>.code`, `abi.decode`, and low-level calls / `FunctionCallOptions` | `<addr>.code` fails closed with `external contract code reads are outside this slice`; `abi.decode(...)` fails closed with `abi.decode is outside this slice`; and `<addr>.call`/`staticcall`/`delegatecall`/`transfer`/`send` and `fn{value: ...}(...)` (`FunctionCallOptions`) fail closed with `external contract calls are outside this slice`. |

### Development slice: dynamic scalar-array and string parameters, string locals/helpers, and `selfbalance` / `tx.origin` context reads

| Supported Solidity | Lowering boundary |
| --- | --- |
| Root and helper `T[] calldata` / `T[] memory` scalar array parameters (`uint8`–`uint256`, `int256`, `address`, `bool`, `bytes32`) | Root `T[] calldata` parameters validate the ABI head, `uint64` length bound, and `32 * length` payload tail via `AbiLowering.scalarArrayCalldataHead`; root `T[] memory` parameters and `calldata`-to-`memory` helper arguments materialize and validate every element word via `AbiLowering.scalarArrayMemoryHead` / `AbiLowering.materializeCalldataScalarArray`. Supports `arr.length`, `arr[i]` (with `Panic(0x32)` bounds check and calldata element validation via `AbiLowering.readScalarArrayElement`), `for (uint256 i = 0; i < arr.length; i++)`, and internal helper forwarding. Nested arrays, narrow signed element arrays (`int8[]`–`int248[]`), `bytes[]` / `string[]`, and array element writes fail closed. |
| Root and helper `string calldata` / `string memory` parameters, `string memory` locals, `bytes(s)` / `string(b)`, and `bytes(s).length` | Root `string calldata` and `string memory` parameters decode via `AbiLowering.bytesCalldataHead` and `AbiLowering.bytesMemoryHead` (`ParamType.string`). Non-reassigned `string memory` locals and `string memory` helper parameters lower to retained `(pointer, size)` byte buffers (`stringBuffers`), supporting string literals, `string(abi.encodePacked(...))`, and single-return `string memory` helpers (`inlineStringFn`). `bytes(s).length` lowers to the buffer's byte length, and `s` / `bytes(s)` can be hashed (`keccak256`) or concatenated in `abi.encodePacked(...)`. Reassigned `string` locals fail closed. |
| `address(this).balance`, `payable(address(this)).balance`, `tx.origin`, and Yul `selfbalance()` / `origin()` | `address(this).balance`, `payable(address(this)).balance`, and Yul `selfbalance()` lower to `Expr.selfBalance`; `tx.origin` (`referencedDeclaration == -15`, `t_magic_transaction`) and Yul `origin()` lower to `Expr.txOrigin`. Covered by `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses` with reflexive `rfl` arm-pin lemmas `evalExpr_selfBalance_arm` and `evalExpr_txOrigin_arm`. External account `<addr>.balance` reads (`external account balance reads are outside this slice`) and `tx.gasprice` (`unsupported transaction context member gasprice`) fail closed. |

### Development slice: `bytes memory` parameters/locals/helpers, `.length` on byte buffers, `bytes.concat` / `string.concat`, `abi.encodeWithSignature`, and `abi.encodeCall`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Root and helper `bytes memory` parameters, `bytes calldata`-to-`bytes memory` copies, and single-return `bytes memory` helpers | Root `bytes memory` parameters decode and materialize calldata into memory at entry via `AbiLowering.bytesMemoryHead`, registering a retained `(pointer, size)` buffer in `byteBuffers` (`pointer := memoryPointer + 32`, `size := lengthBinding`). Initializing a `bytes memory` local or `bytes memory` helper parameter from a `bytes calldata` parameter copies the calldata words into freshly allocated memory via `AbiEncoding.reserve` and `Stmt.forEach`; passing a string literal (`literal_string`) or `bytes memory` buffer to a `bytes memory` helper parameter binds its `(pointer, size)` descriptor in the callee frame; and single-return internal/private/public `bytes memory` helpers inline via `inlineStringFn` (including expression-statement calls whose side-effect prelude is preserved). Indexing (`b[i]`) and reassigning `bytes memory` locals fail closed. |
| `.length` on `bytes memory` locals/parameters and inline encoded byte-buffer expressions | `lowerMember` lowers `<expr>.length` on any `bytes` / `bytes memory` / `bytes calldata` expression (`byteBuffers`, `calldataBytes`, `bytes(s)`, `bytes.concat(...)`, `abi.encode(...)`, `abi.encodePacked(...)`, `abi.encodeWithSelector(...)`, `abi.encodeWithSignature(...)`, `abi.encodeCall(...)`, and `bytes memory` helper calls) to `{ pre := buf.pre, expr := buf.size }`. Direct `.length` on `string` without `bytes(...)` conversion remains rejected by `solc`. |
| `bytes.concat(...)` and `string.concat(...)` builtins | Verified as `ElementaryTypeNameExpression` (`bytes` or `string`) `.concat` calls with `referencedDeclaration == none`. `bytes.concat` accepts `bytes`, `bytes memory`, `bytes calldata`, `bytes32`, `bytes4`, and `literal_string` arguments; `string.concat` accepts `string`, `string memory`, `string calldata`, and `literal_string` arguments. Both lower via `lowerPacked` (evaluating arguments right-to-left to match `solc --via-ir`, allocating a zero-padded output buffer via `AbiEncoding.packedBuffer`, and copying each argument's exact byte length via `AbiEncoding.copyBytes`). Non-byte-buffer uses of `bytes.concat` / `string.concat` and unsupported argument types (such as `uint256`) fail closed with located diagnostics. |
| `abi.encodeWithSignature(sig, args...)` and `abi.encodeCall(ContractOrInterface.fn, (...))` as encoded byte buffers | `abi.encodeWithSignature` lowers `sig` (`string` or string literal) as a byte buffer, computes the 4-byte selector word `keccak256(sigPtr, sigSize) & (0xffffffff * 16^56)` into a 4-byte buffer, validates and lowers each scalar payload argument (`checkEncodingScalar`), and concatenates selector + `32 * n` argument words via `encodeSelectorAndWords`. `abi.encodeCall` resolves the target `ContractOrInterface.fn` `FunctionDefinition` and its 8-hex-char `"functionSelector"` via `lowerMemberFunctionSelector` (requiring a pure contract/interface/library type, `this`, literal, or local/parameter receiver), checks that the second argument's tuple component count matches the target declaration's parameter count, converts each scalar argument to its declared parameter type via `convert pty argTy` (rejecting out-of-range narrow unsigned integer literals), and concatenates the 4-byte selector and `32 * n` words via `encodeSelectorAndWords`. Non-byte-buffer uses and non-scalar payload types fail closed. |

### Development slice: unnamed root dynamic `bytes` and `string` returns (`Stmt.returnBytes`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| Unnamed root `returns (bytes memory)` / `returns (bytes calldata)` and `returns (string memory)` / `returns (string calldata)` | Supported when a root function declares a single unnamed `bytes` or `string` return parameter (`functionDynamicBytesReturn?`) and each reached root `Return` expression satisfies `canLowerDynamicBytesReturnExpr`: string/hex literals, root `bytes` / `string` parameters (`calldata` or `memory`), constant `bytes` / `string` state variables, `bytes(...)` / `string(...)` conversions, `string.concat(...)`, `abi.encode(...)`, `abi.encodePacked(...)`, `abi.encodeCall(...)`, or single-return internal/private/public `bytes memory` / `string memory` helper calls (`_concat`, etc.). Lowers the return expression via `lowerEncodedBytes` into a fresh `_verity_memret_<stem>` pair (`_data_offset := buf.pointer`, `_length := buf.size`), runs any modifier post-placeholder statements (`env.rootPost`), and emits `Stmt.returnBytes "_verity_memret_<stem>"`. `Denote.returnBytesWords` and `Compile.compileStmt` read 32-byte words from memory when `name.startsWith "_verity_memret_"` and right-zero-pad the final partial word (`32 :: length :: paddedWords`), covered by `Coverage.stmtCovered`, `Quote.quoteStmt`, and `TransactionAccess.statementAccesses` with reflexive `rfl` arm-pin lemma `execStmt_returnBytes_arm`. Named dynamic `bytes` / `string` root return parameters, missing root returns, and parameter names starting with `_verity_memret_` fail closed with located diagnostics. |

### Development slice: `string` and `bytes` storage variables (`encoding == "bytes"`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `string` and `bytes` storage state variables (`layout.encoding == "bytes"`, `numberOfBytes == 32`) | Registered in `ImportedContract` with `FieldType.uint256` at their `solc` storage slot (`storageBytesVars`), while `Expr.storageArrayElement field slotExpr` and `Stmt.setStorageArrayElement field slotExpr value` on scalar `FieldType.uint256` fields denote and compile computed-slot `sload`/`tload` and `sstore`/`tstore` directly at `evalExpr slotExpr` (`Denote.evalExpr`, `Denote.execStmt`, `ExpressionCompile.compileStorageArrayElement`, `StorageWrites.compileSetStorageArrayElement`, `SourceSemantics.evalExpr`, `SourceSemantics.execStmt`, `Coverage`, `Quote`, `TransactionAccess`). |
| Storage `string` / `bytes` length reads (`b.length`, `bytes(s).length`, `bytes(string(b)).length`), memory materialization (`lowerStorageBytesRead`), whole-value writes (`s = ...`, `b = ...`), and `delete s` / `delete b` | `lowerStorageBytesLength` decodes the packed Solidity storage header word `raw = sload(slot)` (reverting with `Panic(0x22)` / `0x4e487b710000000000000000000000000000000000000000000000000000000000000022` when `(raw & 1) == ((raw & 255) / 2)` for `0 < (raw & 255) < 64`), returning `(raw & 255) / 2` for short values (`(raw & 1) == 0`) and `raw / 2` for long values (`(raw & 1) != 0`). `lowerStorageBytesRead` allocates a 32-byte-aligned memory buffer via `AbiEncoding.reserve` and either stores `raw & ~255` (short `< 32` bytes) or copies `(len + 31) / 32` words starting at `keccak256(slot)` via `Stmt.forEach` (`keccak256(abi.encode(uint256(slot))) + i`), enabling storage `string` / `bytes` values in `return`, local `string memory` / `bytes memory` initializers, helper arguments, `keccak256(...)`, `abi.encodePacked(...)`, and `bytes.concat` / `string.concat`. `lowerStorageBytesWrite` and `lowerStorageBytesDelete` validate the old storage header (`Panic(0x22)`), zero out any previously occupied long-storage words (`oldWords > newWords` or `newLen < 32`), and write either the packed short header `(firstWord & ~mask) \| (len * 2)` or the long header `len * 2 + 1` plus cleaned payload words at `keccak256(slot) + i`. Storage `bytes` indexing (`b[i]`), `.push` / `.pop`, storage-pointer locals, non-statement assignments, and reads shadowed by unsupported locals/parameters fail closed with located diagnostics. |

### Development slice: multi-statement `InlineAssembly`, Yul locals & full-word local/parameter assignments, `tstore`, `addmod` / `mulmod`, and `*=`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Multi-statement `InlineAssembly` blocks in root, single-return helper, void/multi-return helper, and loop bodies (`lowerAssemblyStmts`) | Supports sequential `YulVariableDeclaration` (`let x := expr` or default-zero `let x`), single-target `YulAssignment` (`x := expr`) to block-scoped Yul locals, the active single-return helper result (`checkYulReturnTarget` + `cleanHelperResultExpr`), or unshadowed full-word (`uint256`, `int256`, `bytes32`) writable Solidity scalar locals and helper/modifier parameters (`inlineAssemblyAssignedIds`), and `YulExpressionStatement` `tstore(slot, val)` (`Stmt.tstore`, covered by `Coverage.executableStmtCovered`, `Coverage.abiHeaderPreservingStmt`, `Quote.quoteStmt`, and `TransactionAccess.statementAccesses` with reflexive `rfl` arm-pin lemma `execStmt_tstore_arm`). Yul assignments to narrow Solidity locals/parameters (`uint8`–`uint248`, `address`, `bool`, `enum`), storage `.slot` / `.offset` references, multi-variable Yul declarations/assignments, and unsupported Yul statements (`if`, `for`, `switch`, `leave`, `mstore`, `sstore`, `revert`) fail closed with located diagnostics. |
| Yul `addmod(a, b, m)` / `mulmod(a, b, m)` and Solidity global `addmod(a, b, m)` / `mulmod(a, b, m)` | `lowerYulAddmod` computes exact 512-bit modular addition `(a + b) % m` (returning `0` when `m == 0` in Yul) via `aMod = a % m`, `bMod = b % m`, `diff = m - bMod`, and `aMod < diff ? aMod + bMod : aMod - diff`. `lowerYulMulmod` computes exact 512-bit modular multiplication `(a * b) % m` (returning `0` when `m == 0` in Yul) via a 256-iteration binary Russian-peasant modular doubling loop (`Stmt.forEach`). Solidity global `addmod` (`referencedDeclaration == -2`) and `mulmod` (`referencedDeclaration == -16`) convert their three arguments to `uint256` in source order, emit `Panic(0x12)` when `m == 0`, and delegate to `lowerYulAddmod` / `lowerYulMulmod` (both in expressions and discarded expression statements). |
| Compound multiplication assignment (`*=`) | Supported on declaration-bound scalar locals, writable helper/modifier parameters (`isCompoundAssignOp`), scalar storage fields, scalar mappings, and unsigned mapping-struct members for `uint8`–`uint256` and `int256`, using `checkedMul` / `checkedSignedMul` in checked mode and wrapping 256-bit (or `2^bits - 1` masked) multiplication in `UncheckedBlock`. |

### Development slice: Yul scratch-space `mstore` / `keccak256`, prefix/postfix `++` / `--`, `bytes32` shifts, and `bytes32` / `int256` / `address` constants

| Supported Solidity | Lowering boundary |
| --- | --- |
| Yul scratch-space `mstore(0x00, v)` / `mstore(0x20, v)` and `keccak256(off, size)` in `InlineAssembly` (`lowerAssemblyStmts`, `lowerYul`) | `lowerAssemblyStmts` admits `mstore(off, val)` when `off` is a pure literal `0` (`0x00`) or `32` (`0x20`), emitting `Stmt.mstore (.literal off) valVal.expr` and recording `yulScratch0` / `yulScratch32` in the active `InlineAssembly` block (`Env.yulScratch0`, `Env.yulScratch32`). `lowerYul` admits `keccak256(off, size)` (`Expr.keccak256`) over `(0, 32)`, `(32, 32)`, or `(0, 64)` only when the corresponding scratch-space word(s) have already been written in the same Yul block (`keccak256 requires scratch-space words 0x00..0x3f to be written in the same Yul block`), preventing reads of uninitialized or ABI-managed memory. Non-scratch `mstore` offsets or non-literal `keccak256` ranges fail closed (`only scratch-space mstore at 0x00 or 0x20 is supported`, `only scratch-space keccak256 over 0x00..0x3f is supported`). |
| Prefix (`++x`, `--x`) and postfix (`x++`, `x--`) increment/decrement in expressions and expression statements (`lowerIncDecExpr`) | Supported on writable `uint8`–`uint256` and `int256` scalar locals and helper/modifier parameters (`bodyCompoundAssignedIds`), scalar storage fields, scalar mappings (1 or 2 keys), and unsigned mapping-struct scalar members. Evaluates the target's prior value into `oldVar`, applies `combineCompound ("+=" \| "-=") ty (.localVar oldVar) (.literal 1)` (preserving checked `Panic(0x11)` vs `UncheckedBlock` wrapping), writes back the updated value, and yields the updated value for prefix (`++x`, `--x`) or `oldVar` for postfix (`x++`, `x--`). `assignmentIn` includes `++` and `--` so multi-operand / multi-argument expressions with side-effecting increments or decrements fail closed unless evaluation order is explicit. |
| `bytes32` shifts (`<<`, `>>`, `<<=`, `>>=`) and `bytes32` / `int256` / `address` constant state variables (`numericConstants`) | `lowerBinary`, `combineCompound`, and `lowerCompoundAssignment` support `<<`, `>>`, `<<=`, and `>>=` on `bytes32` with unsigned shift amounts (`Expr.shl rhs lhs` / `Expr.shr rhs lhs`). `numericConstants` and `lowerRef` admit `bytes32`, `int256` / `int`, and `address` / `address payable` `constant` declarations, converting the initializer via `convert declared (← mType initializer) (← lowerExpr initializer) initializer` while rejecting non-empty initializer preludes and narrow signed/fixed-bytes constant types (`int8`–`int248`, `bytes1`–`bytes31`). |

### Development slice: dynamic memory scalar array allocation/writes (`new T[](len)`), extended mapping keys/struct members, and terminal root named-return `InlineAssembly`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Dynamic memory scalar array allocation (`T[] memory a = new T[](len)`), element writes (`a[i] = val` / `delete a[i]`), and pure index preludes (`a[idx++]`) | `lowerLocal` supports non-reassigned `T[] memory` declarations initialized with `new T[](len)` when `T` is `uint8`–`uint256`, `address` / `address payable`, `bool`, or `bytes32` (`newArrayElementType?`). Evaluates `len` to `uint256`, guards `len <= 2^64 - 1` (`Panic(0x41)`), initializes free-memory pointer `0x40` to `0x80` if zero, checks `32 + 32 * len` allocation overflow (`Panic(0x41)`), bumps `0x40`, stores `len` at `ptr`, zero-initializes `len` words via `Stmt.forEach`, and registers an `inMemory := true` `ScalarArrayParam` in `scalarArrays`. `lowerEffect` supports `a[i] = val` and `delete a[i]` on `inMemory := true` scalar arrays with `i < a.length` bounds checks (`Panic(0x32)`) and boolean `0`/`1` normalization. `lowerRef` `IndexAccess` on `.scalarArray` allows index expressions with empty base preludes (such as `leaves[leafPos++]` and `hashes[hashPos++]`). Signed/nested `new` array allocations, reassigned array locals, and `calldata` array element writes fail closed. |
| Extended mapping key types (`mappingKey`) and mapping struct member types (`buildField`, `memberRead`, `lowerEffect`) | `mappingKey` accepts `address`, `address payable`, `contract` / `interface` types, `bytes32`, `int256`, `bool`, `enum` types, and `uint8`–`uint256` as one- and two-key mapping keys; narrow signed (`int8`–`int248`), fixed-bytes (`bytes1`–`bytes31`), and reference keys fail closed. `buildField` accepts `uint8`–`uint256`, `int256`, `address`, `address payable`, `contract` / `interface` types, `bytes32`, and `bool` as packed or full-word mapping-struct members, recording `booleanMembers` on `FieldInfo` so `memberRead` and `lowerEffect` normalize boolean struct member reads and writes with `Expr.logicalNot (.logicalNot ...)`. |
| Terminal root `InlineAssembly` assigning to a single named scalar return variable | When a root function has a single named scalar return parameter (`rootNamedReturn`), empty modifier post-statements (`rootPost.isEmpty`), and a terminal `InlineAssembly` statement that only assigns to the return declaration without reading it in Yul (`yulOnlyAssignsDecl`), `lowerRootStatements` routes the assembly block through `helperResult := some (rbinding, rty)` and `cleanHelperResultExpr` before `lowerRoot` emits `Stmt.returnValues`, matching `solc` ABI return masking on narrow return types (such as `address`) while rejecting Yul reads of narrow root return variables. |

### Development slice: user-defined value types (`type T is U`), direct parameter assignments, chained/conditional multi-returns, zero-arg custom-error helpers, Yul memory-array `keccak256`, and struct-array element helper calls

| Supported Solidity | Lowering boundary |
| --- | --- |
| User-defined value types (`type T is U`, `T.wrap(x)`, `T.unwrap(v)`, `using L for T`) | `index` records `UserDefinedValueTypeDefinition` nodes in `userValueTypeById` and `userValueTypes`, mapping both qualified (`Contract.T`) and unqualified (`T`) names to their underlying elementary type string `U`. When `U` is a supported non-enum scalar (`uint8`–`uint256`, `int256`, `address`, `bool`, `bytes32`), `mType` normalizes UDVT type descriptions to `U`, `selectFunction` matches either the UDVT name or `U`, and `lowerCall` lowers `T.wrap(arg)` and `T.unwrap(arg)` via `convert U (← mType arg) (← lowerExpr arg) arg`. UDVTs with unsupported underlying types (such as `bytes16` or `int128`) fail closed. |
| Direct scalar parameter assignments (`param = rhs`) in root functions, helpers, and modifiers | `bindHelperParams`, `lowerModifier`, and `lowerRoot` materialize scalar parameters into writable local bindings (`writableLocals`) whenever `bodyCompoundAssignedIds body` or `bodyDirectAssignedIds body` contains the parameter declaration ID (`||` instead of `&& !`), initializing the local to the incoming parameter value so both reads before assignment and subsequent `=` / compound assignments use the same mutable binding. `delete param` remains rejected (`only materialized scalar locals are writable` / `only declaration-bound scalar locals are writable`). |
| Chained and conditional multi-return statements (`return _pair(...);`, `return cond ? _pair(...) : (a, b);`) in helpers and roots | Both `lowerVoidHelperFrom` (when `multiHelperResults` is active) and `lowerRootStatements` (when `rootReturnTypes.size > 1`) route non-`TupleExpression` return expressions through `lowerMultiBranch` with expected component types, supporting direct multi-return helper forwarding and `Conditional` (`? :`) expressions whose branches are tuples or multi-return helper calls of matching arity. |
| Pure/view zero-argument scalar helper calls and `tx.origin` in custom-error revert arguments (`revert Unauthorized(_msgSender(), ...)`) | `isDirectErrorScalar` admits `tx.origin` (`referencedDeclaration == -26`) and zero-argument internal/private `pure` or `view` helper calls returning a single supported scalar (such as `_msgSender()`), while stateful (`nonpayable`/`payable`), parameterized, or external calls in custom-error arguments fail closed. |
| Yul `keccak256(add(arr, 0x20), mul(mload(arr), 0x20))` over dynamic memory scalar arrays (`yulMemoryArrayPayloadSlice?`) | `Env.yulMemoryArrays` maps unshadowed `T[] memory` variable names (`new T[](len)` locals and `T[] memory` parameters) to their `memoryPointer` binding (clearing entries on local/parameter shadowing or Yul `let` shadowing). In `lowerYul`, `keccak256(ptrNode, sizeNode)` recognizes `add(arr, 0x20)` (or `add(0x20, arr)`) paired with `mul(mload(arr), 0x20)` (or `mul(0x20, mload(arr))`) for the same `arr` identifier and lowers to `Expr.keccak256 (.add (.localVar arrayPtr) (.literal 32)) (.mul (.mload (.localVar arrayPtr)) (.literal 32))`. Mismatched array identifiers or arbitrary pointer arithmetic fail closed (`unsupported Yul keccak256 arguments`). |
| Passing struct-array elements (`market.collaterals[i]`) to internal struct helper parameters (`.abiElement` in `lowerCallArgs` / `bindHelperParams`) | `lowerCallArgs` lowers `IndexAccess` on a schema-validated struct array (`m.items[i]`, `.abiElement`) to `CallArg.abiElement`. `bindHelperParams` verifies that the element struct's AST declaration ID matches the callee parameter's struct declaration ID, binds `calldata`-to-`calldata` and `memory`-to-`memory` element pointers in `abiElements`, and materializes `calldata`-to-`memory` element arguments via `AbiRootLowering.materializeElementFromCalldata`. `memory`-to-`calldata` conversions fail closed. |

### Development slice: nested 1-key scalar mappings in storage structs, `bytes4` scalars, and `type(I).interfaceId`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Nested 1-key scalar mappings inside mapping-backed storage structs (`struct RoleData { mapping(address => bool) hasRole; ... }`) | `buildField` decodes `mapping(K => V)` members inside mapping-backed structs (`StructMappingInfo` with `wordOffset`, `keyType`, `valueType`, `valueBits`, `booleanValue`) when `K` is a supported `mappingKey` and `V` is a supported scalar (`uint8`–`uint256`, `int256`, `address` / contract / interface, `bytes32`, `bool`). Accessed struct mappings are recorded in `usedStructMappings` (removing them from `report.opaqueMembers` while keeping unreferenced struct mappings opaque) and enable the synthetic `_verity_raw_storage` (`FieldType.uint256`) slot channel (`usedRawStorage`). `computeStructMappingLeafSlot` hashes outer mapping key(s) via `keccak256(abi.encode(k, slot))`, adds `wordOffset`, and hashes `keccak256(abi.encode(innerKey, structSlot + wordOffset))`. `readStructMappingElement`, `writeStructMappingElement`, `lowerEffect`, `lowerCompoundAssignment`, and `lowerIncDecExpr` support scalar reads, `=`, `delete`, compound assignments, and `++`/`--` (with bit-width masking and boolean `0`/`1` normalization). Unindexed struct-mapping references and whole-struct `delete m[k]` on structs with mapping members fail closed (`cannot delete mapping struct with mapping members`). |
| `bytes4` scalar type (`ParamType.bytesN 4`, `BytesN 4`) | `paramType "bytes4" = some (.bytesN 4)` with `Word (BytesN 4)` accessor bridge, preserving canonical `"bytes4"` ABI signature rendering (`supportsInterface(bytes4)`, etc.). Root `bytes4` parameters enforce `solc`'s entry calldata check `(calldataload(offset) & (2^224 - 1)) == 0` (`bytes4Params`); named helper/root returns clean trailing bits via `cleanHelperResultExpr`; uninitialized `bytes4` locals default to `0`; `bytes4` constants (`numericConstants`) and `0xXXXXXXXX` hex literals (`convert "bytes4"`) left-align to `val * 16^56`; explicit casts support `bytes4(bytes32Val)` (`bitAnd (0xffffffff * 16^56)`), `bytes32(bytes4Val)`, `uint32(bytes4Val)` (`shr 224`), and `bytes4(uint32Val)` (`shl 224`); bitwise `&`, `\|`, `^`, `~`, `&=`, `\|=`, `^=` mask results to the upper 4 bytes (`0xffffffff * 16^56`); comparisons (`==`, `!=`, `<`, `>`, `<=`, `>=`) require both operands to be `bytes4` (rejecting implicit `int_const` operands); and `abi.encode`, `abi.encodePacked`, and `bytes.concat` accept `bytes4` scalars (`scalarPackedWidth "bytes4" = some 4`). |
| `type(I).interfaceId` constant evaluation (`lowerInterfaceId`) | Supported in `lowerExpr`, `checkEncodingScalar`, and `lowerErrorArguments` when `I` resolves to a `ContractDefinition` with `contractKind == "interface"`. Collects all `FunctionDefinition` nodes directly declared in `I`, parses each 8-hex-digit `"functionSelector"`, XORs the 32-bit selector words (`Nat.xor`), and left-aligns the result (`acc * 16^56`) as a `bytes4` literal. Non-interface contracts or missing function selectors fail closed with located diagnostics. |

### Development slice: top-level storage structs, flat scalar-member `memory` struct locals, whole-struct storage assignment/`delete`, standalone `.selector` expressions, Yul memory-array element loads, and Yul fixed-prefix `keccak256`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Top-level storage struct state variables (`RoyaltyInfo private _defaultRoyaltyInfo;`, `SPath.zero`) | `buildTopStructField` decodes top-level `t_struct(...)` layout items via `decodeStructLayoutMembers` (`keyCount = 0`). When a top-level struct is referenced, `importSlice` emits a scalar `Field` (`FieldType.uint256`, `slot = some (info.slot + member.wordOffset)`, `packedBits = member.packed`) per scalar/expanded-array member under `_verity_struct_<field>_<member>` (`topStructMemberFieldName`), while rejecting user storage declarations that start with `_verity_struct_`. `memberRead`, `lowerEffect`, `lowerCompoundAssignment`, `lowerIncDecExpr`, `computeStructMappingLeafSlot`, and `lowerLocal` support member reads/writes, nested struct-mapping/fixed-array accesses, `storage` local aliases, and whole-struct reads/writes/`delete` on `SPath.zero`. |
| Flat scalar-member `memory` struct locals, positional `StructName(...)` constructors, and whole-struct storage assignment/`delete` (`FlatStructLocal`, `lowerFlatStructValue`, `writeWholeStorageStruct`) | Local `StructName memory s = init;` declarations where `StructName` has only supported non-enum scalar members (`paramType mTy`) and `init` is either a positional `structConstructorCall` (`StructName(a, b)`) or a scalar-member storage struct path (`_tokenRoyaltyInfo[id]`, `_defaultRoyaltyInfo`) materialize one writable scalar local binding per member (`flatStructs`, `FlatStructLocal`). `s.member` reads and writes the corresponding scalar binding, `s = rhs` updates all member bindings from a positional constructor or storage struct read (rejecting local-to-local `s2 = s1` aliasing so value-vs-reference semantics can never diverge), and `writeWholeStorageStruct` lowers `storageStruct = rhs` and `delete storageStruct` across all scalar members (`keyCount` `0`, `1`, or `2`). Named struct constructor arguments (`StructName({b: 2, a: 1})`) and structs with mapping/array/opaque members fail closed. |
| Standalone `.selector` member access as a `bytes4` scalar expression (`this.onERC721Received.selector`, `IERC1155Receiver.onERC1155Received.selector`, `CustomError.selector`) | `lowerSelectorMemberAccess` lowers `.selector` `MemberAccess` nodes with `typeDescriptions.typeString == "bytes4"` when the base is a pure receiver `MemberAccess` (`isPureSelectorReceiver`: contract/interface type, `this`, or a pure local/parameter) referencing a function, public state variable (`"functionSelector"`), or custom error (`"errorSelector"`), or an `Identifier` referencing a custom error, left-aligning the 8-hex-digit selector to `word * 16^56`. Non-pure receivers or non-member bases fail closed. |
| Yul 32-byte-strided memory-array element loads (`res := mload(add(add(arr, 0x20), mul(pos, 0x20)))`, `yulMemoryArrayElementLoad?`) | In `lowerYul`, `mload(addr)` matches `add(add(arr, 0x20), mul(pos, 0x20))` (with commutative operand order for `add` and `mul`) when `arr` resolves in `yulMemoryArrays` to an unshadowed `T[] memory` binding (`uint256[]`, `address[]`, etc.), lowering to `Expr.mload (.add (.add (.localVar arrayPtr) (.literal 32)) (.mul posExpr (.literal 32)))`. Non-`0x20` strides or non-array pointers fail closed (`unsupported Yul builtin mload`). |
| Yul fixed-prefix scratch-space and free-memory `keccak256` blocks (`MessageHashUtils.toEthSignedMessageHash(bytes32)`, `MessageHashUtils.toTypedDataHash(bytes32, bytes32)`, `lowerYulPrefixKeccakBlock?`) | Recognizes (1) 3-statement Yul blocks `mstore(0x00, "<k-byte prefix>"); mstore(k, msgHash); dst := keccak256(0x00, k + 0x20)` (`0 < k < 32`) and lowers them to exact scratch-space packing (`mstore(0, prefixWord \| (msgHash >> (8*k)))`, `mstore(32, msgHash << (8*(32-k)))`, `keccak256(0, k + 32)`), and (2) 5-statement EIP-712 Yul blocks `let ptr := mload(0x40); mstore(ptr, "<k-byte prefix>"); mstore(add(ptr, k), domSep); mstore(add(ptr, k + 0x20), structHash); dst := keccak256(ptr, k + 0x40)` (`0 < k < 32`) and lowers them to free-memory-pointer-preserving writes at `mload(64)` followed by `keccak256(ptr, k + 64)`. Mismatched offsets or lengths fail closed. |

### Development slice: `storage` struct / `bytes` / `string` helper parameters, flat scalar-member `memory` struct helper parameters, and `bytes32(bytes)` / `bytes4(bytes)` casts

| Supported Solidity | Lowering boundary |
| --- | --- |
| Internal/private/library `StructName storage` helper parameters (`BitMaps.BitMap storage`, `DoubleEndedQueue.Bytes32Deque storage`, `using L for S` receiver syntax) | `lowerCallArgs` lowers top-level (`SPath.zero`), 1-key (`SPath.one`), and 2-key (`SPath.two`) storage struct paths and `storage` struct local/parameter aliases (`Ref.structSlot`) to `CallArg.storageStruct`, capturing mapping keys into fresh temporaries at the call boundary (`captureStoragePath`). `bindHelperParams` verifies that the argument's `FieldInfo.structType` matches the callee parameter's `t_struct(...)` type and binds the resolved `SPath` in `structAliases`, enabling scalar member reads/writes/`delete`/compound assignments, nested struct-mapping accesses (`BitMaps`), fixed-array accesses, whole-struct `delete` (`DoubleEndedQueue.clear`), and forwarding to nested `storage` struct helpers. Top-level structs whose only members are nested mappings (`BitMaps.BitMap`) omit redundant scalar field definitions while emitting `_verity_raw_storage`. Reassigning a `storage` struct parameter (`p = other`) fails closed (`reassigned storage struct parameters are outside this slice`). |
| Internal/private/library `StructName memory` helper parameters for flat scalar-member structs (`FlatStructLocal` / `CallArg.flatStruct`) | When a `StructName memory` helper parameter is not covered by the existing `AbiRootLowering` calldata/memory root-ABI schema, `lowerCallArgs` accepts a `FlatStructLocal` identifier, a positional `StructName(...)` constructor, or a storage-to-memory copy of a scalar-member storage struct (`lowerFlatStructValue`), evaluating and converting all scalar members at the call site into `CallArg.flatStruct`. `bindHelperParams` binds fresh per-member local variables in `flatStructs` and rejects helpers that reassign the struct parameter (`reassigned struct parameters are outside this slice`). Storage-to-memory copies of structs with mapping/array/opaque members fail closed (`storage struct with non-scalar members cannot be copied to memory in this slice`). |
| Internal/private/library `bytes storage` and `string storage` helper parameters (`ShortStrings.byteLengthWithFallback`, `ShortStrings.toStringWithFallback`, `ShortStrings.toShortStringWithFallback`) | `lowerCallArgs` resolves top-level `bytes` / `string` storage variables and `storage` parameter aliases (`storageBytesVars`) to `CallArg.storageBytes`. `bindHelperParams` binds the `StorageBytesInfo` descriptor in the callee's `storageBytesVars`, enabling `.length` / `bytes(store).length`, memory materialization (`lowerStorageBytesRead`), whole-value storage writes (`store = val`, when the target is a direct storage variable rather than a storage-pointer parameter), `delete store`, and forwarding to nested helpers. Because `=` on a `string storage` / `bytes storage` helper parameter (`t_string_storage_ptr` / `t_bytes_storage_ptr`) rebinds the local storage pointer in Solidity rather than writing to storage, helpers that assign to a `bytes storage` or `string storage` parameter fail closed (`reassigned storage bytes parameters are outside this slice` / `reassigned storage string parameters are outside this slice`). |
| Explicit `bytes32(bytesVal)` and `bytes4(bytesVal)` casts (`ShortStrings.toShortString`) | `lowerConversion` supports `bytes32(...)` and `bytes4(...)` when the inner argument is a `bytes` / `bytes memory` / `bytes calldata` / `bytes storage` expression (`lowerEncodedBytes`). Evaluates the byte buffer once (`ptr`, `size`), loads the first 32-byte word when `size > 0` (`0` when `size == 0`), zeroes trailing bytes beyond `size` when `size < 32` (`word & ~(2^(8*(32 - size)) - 1)`), and masks to the upper 4 bytes (`0xffffffff * 16^56`) for `bytes4(...)`. |

### Development slice: ERC-7201 / `StorageSlot` raw-slot struct pointers (`r.slot := slot`), `StorageSlot.StringSlot` / `StorageSlot.BytesSlot` dynamic storage, `ShortStrings.toString`, and `$` identifiers

| Supported Solidity | Lowering boundary |
| --- | --- |
| ERC-7201 namespaced storage and `StorageSlot` struct pointer helpers (`function _getVaultStorage() private pure returns (VaultStorage storage $) { assembly { $.slot := SLOT } }`, `StorageSlot.getAddressSlot(slot).value`, `SPath.rawSlot`) | `classifyStorageSlotReturnHelper` recognizes internal/private/library helpers that return a single named `StructName storage r` parameter and have a 1-statement `Block` containing a 1-statement `InlineAssembly` block `r.slot := expr` (`yulSlotAssignRhs?`). For struct definitions whose members are supported scalars, packed scalars (`buildRawStructField`, computing exact word and byte offsets via `solc`'s 32-byte packing rules), and 1-key or 2-key scalar mappings (`StructMappingInfo` with `innerKey2Type?`), `lowerStorageSlotPointerHelper` inlines the helper call, evaluates `expr` as a `uint256` slot binding, sets `usedRawStorage := true`, and returns `Ref.structSlot #[] (.rawSlot info slotBinding)`. `readRawSlotScalarMember` and `writeRawSlotScalarMember` read, mask, shift, sign-extend (`int256`), boolean-normalize, and pack/unpack scalar members on `_verity_raw_storage[baseSlot + wordOffset]`; `computeStructMappingLeafSlot` hashes `keccak256(abi.encode(k1, baseSlot + wordOffset))` (and `keccak256(abi.encode(k2, ...))` for 2-key mappings); and `lowerLocal`, `lowerCallArgs`, `writeWholeStorageStruct`, `lowerCompoundAssignment`, and `lowerIncDecExpr` support `StructName storage $ = _getStorage();`, helper forwarding, scalar/packed member updates, and whole-struct writes/`delete`. Nested struct-valued mappings inside ERC-7201 raw-slot structs or multi-statement slot-pointer assembly helpers fail closed with located diagnostics. |
| `StorageSlot.StringSlot` and `StorageSlot.BytesSlot` dynamic `string` / `bytes` storage wrappers (`StorageSlot.getStringSlot(slot).value`, `StorageSlot.getBytesSlot(slot).value`, `SPath.bytesSlot`) | When a `r.slot := expr` helper returns a `StructName storage` whose `StructDefinition` has a single `string` or `bytes` member named `value` (`classifyStorageSlotReturnHelper` returning `.bytesStorageSlot`), `lowerStorageSlotPointerHelper` yields `Ref.structSlot #[] (.bytesSlot slotBinding isString)`. `MemberAccess` `.value` resolves to `Ref.storageBytes pre { name := rawStorageFieldName, slotExpr := .localVar slotBinding, isString }` (`StorageBytesInfo.slotExpr`), enabling `.value.length` / `bytes(...value).length`, memory reads (`lowerStorageBytesRead`), whole-value writes (`StorageSlot.getStringSlot(slot).value = s`), `delete StorageSlot.getBytesSlot(slot).value`, and passing `.value` to `string storage` / `bytes storage` helpers (such as `ShortStrings.toStringWithFallback(sstr, StorageSlot.getStringSlot(slot).value)`). Wrapper structs with extra members or members other than `.value` fail closed (`StorageSlot bytes/string wrapper struct must have a single value member`). |
| `ShortStrings.toString(ShortString)` (`string memory str = new string(32); assembly { mstore(str, len) mstore(add(str, 0x20), sstr) }`, `yulShortStringsAllocPtrs`, `lowerYulShortStringStoreBlock?`) | `lowerLocal` admits `string memory s = new string(cap)` / `bytes memory b = new bytes(cap)` when `cap` is the literal `32`, reserving 64 bytes via `AbiEncoding.reserve`, storing initial length `32` and zeroed payload word, and registering `s` in `Env.yulShortStringsAllocPtrs` and `bytesVars`. `lowerYulShortStringStoreBlock?` recognizes the 2-statement `InlineAssembly` block `mstore(str, lenExpr); mstore(add(str, 0x20), wordExpr)` on an unshadowed `yulShortStringsAllocPtrs` buffer, updating `mstore(ptr, lenExpr)` and `mstore(ptr + 32, wordExpr)` and refreshing the `MemoryBuffer` length in `bytesVars` so returning `str` or passing `str` to `bytes(str)` / `keccak256` / `abi.encodePacked` observes the updated dynamic length. Non-`32` capacity literals or mismatched `mstore` targets fail closed (`only new string(32) / new bytes(32) for ShortStrings is supported in this slice`). |
| `$` in Solidity local variable and parameter identifiers (`VaultStorage storage $ = _getVaultStorage();`) | `lowerLocal` allows `$` alongside alphanumeric characters and `_` in Solidity identifier names, while `freshFor` sanitizes or falls back to `fresh` whenever a source name contains characters outside `[a-zA-Z0-9_]` so generated Yul variable names remain valid identifiers. |

### Development slice: dynamic scalar storage arrays (`T[]`), recursive nested storage structs, `Arrays.unsafeAccess`, `EnumerableSet` / `EnumerableMap`, and unnamed root dynamic scalar array returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Top-level and struct-member dynamic scalar storage arrays (`T[]`, `layout.encoding == "dynamic_array"`, `StructDynamicArrayInfo`) | `buildField`, `decodeStructLayoutMembers`, and `resolveRawStructInfo` decode 1-D dynamic storage arrays `T[]` (`dynamicStorageArrayElement?`: `uint8`–`uint256`, `int256`, `address` / contract, `bool`, `bytes32`) at top level (`FieldInfo.dynamicArrayElemType`), inside top-level or mapping-backed structs (`FieldInfo.structDynamicArrays`), and inside ERC-7201 raw-slot structs (`RawStructInfo.dynamicArrays`). Element packing (`dynamicStorageArrayElemLayout`: `perWord = max 1 (32 / (bits / 8))`) computes exact storage slot `keccak256(abi.encode(slot)) + index / perWord` and intra-word shift `((index % perWord) * bits)` on `_verity_raw_storage`. Supports `.length` (`readStorageDynamicArrayLength`), `arr[i]` reads (`readStorageDynamicArrayElement` with `Panic(0x32)` bounds check), `arr[i] = val` / `delete arr[i]` / compound assignments / `++` / `--` (`writeStorageDynamicArrayElement`), `arr.push(val)` and `arr.push()` (`pushStorageDynamicArray`, incrementing length and writing at `oldLen`), `arr.pop()` (`popStorageDynamicArray` with `Panic(0x31)` on empty array, clearing element `newLen`), `delete arr` (`deleteStorageDynamicArray`, zeroing `(len + perWord - 1) / perWord` slots and setting length to `0`), and storage-to-memory copies (`T[] memory m = arr;` and `T[] memory` helper arguments via `copyStorageDynamicArrayToMemory`). Multi-dimensional or struct-element dynamic storage arrays and whole-array assignment `arr = other` fail closed with located diagnostics. |
| Recursive nested struct members in storage structs (`struct UintSet { Set _inner; }`, `struct AddressToUintMap { Bytes32ToBytes32Map _inner; }`) and `StructName storage` return helpers | `decodeStructLayoutMembers` and `resolveRawStructInfo` recursively flatten nested `t_struct(...)` members using qualified member paths (`subPrefix.member` / `qualifySPathMember` / `appendSPathSub` for `SPath.zero`, `SPath.one`, `SPath.two`, and `RawStructSubStructInfo` word offsets for `SPath.rawSlot`), enabling arbitrary-depth `set._inner._values`, `map._inner._keys._inner._positions[k]`, and `$.borrowerSet` accesses. `inlineStorageRefFn` inlines internal/private/library helpers that return `StructName storage` or `T[] storage` pointers (`StorageSlot.getBytes32Slot`, `Arrays.unsafeAccess`). |
| `T[] storage` helper parameters, local aliases, `arr.slot` in `InlineAssembly`, and `uint256[] memory` / `bytes32[] memory` pointer reinterpretation (`EnumerableSet.values`) | `lowerCallArgs`, `bindHelperParams`, and `lowerLocal` bind non-reassigned `T[] storage` parameters and locals in `storageDynamicArrayVars` and expose `<name>.slot` in `Env.yulNames` (`Arrays.unsafeAccess(bytes32[] storage arr, uint256 pos)`). Single-return helpers returning `T[] memory` inline via `inlineScalarArrayFn` (supporting `return storageArr;`, `return memArr;`, and `return helper(...);`). `lowerYulScalarArrayAliasBlock?` recognizes the 1-statement `InlineAssembly` block `assembly ("memory-safe") { result := store }` in `EnumerableSet.values(UintSet storage)` / `values(AddressSet storage)` when `store` and `result` are unshadowed 32-byte-word memory scalar arrays (`bytes32[]`, `uint256[]`, `address[]`), rebinding `result` to `store`'s `memoryPointer` and `lengthBinding`. Reassigned `T[] storage` parameters or locals fail closed. |
| Unnamed root dynamic scalar array returns (`returns (T[] memory)`) | Supported when a root function declares a single unnamed `T[] memory` return parameter (`functionDynamicScalarArrayReturn?`). Non-empty root bodies lower each reached `Return` statement (`canLowerDynamicScalarArrayReturnExpr`: local `T[] memory` variable, storage `T[]` copy, or `T[] memory` helper call such as `activeTrancheIds.values()`) into a fresh `_verity_arrret_<stem>` pair (`_data_offset := ptr + 32`, `_length := len * 32`), run `env.rootPost`, and emit `Stmt.returnBytes "_verity_arrret_<stem>"` (`Denote.returnBytesWords` and `Compile.compileStmt` emit `32 :: wordCount :: words` for `_verity_arrret_`, matching `solc` ABI encoding of `T[]`). |

### Development slice: dynamic storage arrays of scalar-member structs (`S[]`), struct-valued mappings inside storage structs, `Checkpoints._unsafeAccess`, binary-search `while (low < high)` loops, named struct constructors, and flat-struct helper returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Dynamic storage arrays of scalar-member structs (`S[]`, `Checkpoints.Checkpoint208[]`, `TrancheRecord[]`) at top level, inside storage structs, and inside ERC-7201 raw-slot structs (`FieldInfo.dynamicArrayStructId`, `StructDynamicArrayInfo.elemStructId`) | `buildField`, `decodeStructLayoutMembers`, and `resolveRawStructInfo` accept 1-D dynamic storage arrays `S[]` when `S` is a struct whose members are all supported scalars (`elemInfo.mappings.isEmpty && elemInfo.dynamicArrays.isEmpty && elemInfo.subStructs.isEmpty && !elemInfo.scalars.isEmpty && elemInfo.wordCount > 0`) and `base.numberOfBytes == elemInfo.wordCount * 32`. `storageDynamicStructElementPath` checks `index < len` (`Panic(0x32)`) and resolves `arr[index]` to `SPath.rawSlot elemSid (keccak256(abi.encode(arrSlot)) + index * wordCount)`, enabling member reads/writes, whole-struct reads (`S memory s = arr[i];`), whole-struct writes (`arr[i] = s`), and `delete arr[i]` (zeroing all `wordCount` slots). `pushStorageDynamicStructArray` lowers `arr.push(s)` and `arr.push()` (returning `SPath.rawSlot elemSid (keccak256(abi.encode(arrSlot)) + oldLen * wordCount)` for `S storage p = arr.push();` and chained `arr.push().member = v`), `popStorageDynamicArray` zeroes all `wordCount` slots of `newLen` on `arr.pop()` (`Panic(0x31)` on empty array), and `deleteStorageDynamicArray` zeroes `oldLen * wordCount` words on `delete arr`. `S[] storage` parameters and locals bind `(fieldName, slotExpr, elemTy, some elemSid)` in `storageDynamicArrayVars` and expose `<name>.slot` in `Env.yulNames`. Struct elements with nested arrays, mappings, or sub-structs fail closed (`unsupported storage encoding dynamic_array`). |
| Struct-valued mappings inside storage structs and ERC-7201 raw-slot structs (`mapping(address => Checkpoints.Trace208) delegateCheckpoints`, `StructMappingInfo.valueStructId`) | `resolveRawStructInfo` and `decodeStructLayoutMembers` accept `mapping(K => V)` struct members when `K` is a supported `mappingKey` and `V` resolves to a supported `RawStructInfo` (`valueStructId := some valSid`). Indexing `s.map[k]` in `lowerRef` hashes `leafSlot := keccak256(abi.encode(k, mapBaseSlot))` and returns `Ref.path (...) (.rawSlot valSid (.localVar leafSlot))`, enabling nested struct member, dynamic-array, and helper-receiver accesses such as `$.delegateCheckpoints[voter].push(...)` and `$.delegateCheckpoints[voter].upperLookup(...)`. |
| Prefix Yul statements before `result.slot := ...` in storage-pointer helpers (`Checkpoints._unsafeAccess`) | `inlineStorageRefFn` supports internal/private/library helpers returning `StructName storage result` whose `InlineAssembly` block executes prefix Yul statements (such as `mstore(0, self.slot)`) before a final `result.slot := add(keccak256(0, 0x20), pos)` assignment, lowering the prefix statements via `lowerYulStmtSlice` and returning `SPath.rawSlot retStructId (.localVar slotTmp)`. Statements after `result.slot := ...` or missing slot assignments fail closed (`storage pointer helper assembly must end with a single slot assignment`). |
| Binary-search `while (low < high)` / `while (high > low)` loops (`Checkpoints._upperBinaryLookup`, `Checkpoints._lowerBinaryLookup`) | `lowerWhile` recognizes `while (low < high)` and `while (high > low)` over distinct writable unsigned integer locals/parameters `low` and `high` of matching bit width (`isBinarySearchMidpointExpr`, `isBinarySearchStepStmt`): the loop body must be `[VariableDeclarationStatement mid = midpoint(low, high), IfStatement ...]` where `midpoint(low, high)` is `(low + high) / 2`, `(low + high) >> 1`, `(low & high) + (low ^ high) / 2`, `low + (high - low) / 2`, or a 2-argument pure helper returning that midpoint (`Math.average(low, high)`), and the `if / else` branches assign `high = mid` in one branch and `low = mid + 1` (or `1 + mid`) in the other while leaving `low`, `high`, and `mid` otherwise unmodified. Lowers to `let bound := sub high low; forEach iter bound [ite (lt low high) body []]`, which executes at most `high - low` iterations (and strictly halves `high - low` on every active step). Non-narrowing branches or modified midpoint variables fail closed. |
| Named struct constructor arguments (`StructName({fieldB: b, fieldA: a})`) and helpers returning flat `StructName memory` (`inlineFlatStructFn`) | `lowerFlatStructValue` supports named `structConstructorCall` arguments (`names.size == args.size`) when every argument is pure/stateless (`!statefulCallIn arg && !assignmentIn arg`), evaluating each argument once into a temporary in call-site order and assembling member values in struct declaration order (rejecting stateful or assignment arguments so evaluation order can never diverge). `inlineFlatStructFn` and `lowerVoidHelperFrom` (`flatStructHelperResult`) inline internal/private/library helpers returning a single flat scalar-member `StructName memory` (`Checkpoints.at`, `_makeRecord`), supporting named and unnamed return parameters, `if / else` early returns, conditional struct expressions (`cond ? s1 : s2`), member projections (`s.at(0)._value`), local initializations (`Checkpoint208 memory c = _unsafeAccess(...);`), and discarded flat-struct/multi-return helper calls in `lowerEffect`. |

### Development slice: `TickLib` bounded sign-flip self-calls (`wExp(-x)`), `while (low != high)` binary search with `unchecked` blocks, 3-key scalar and struct mappings, and top-level fixed-size unsigned scalar storage arrays (`uintN[L]`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| Bounded 1-step `int256` sign-flip self-calls (`TickLib.wExp(int256 x)`: `if (x < 0) return FixedPointMathLib.divWad(1e18, wExp(-x));`, `inlineSignFlipSelfCallFn?`, `inlineSelfSignFlipTarget`) | `inlineSignFlipSelfCallFn?` recognizes single-return internal/private/library helpers with one `int256` parameter `x` (neither directly nor compound-assigned in the body) whose leading statement is `if (x < 0)` (or `if (0 > x)`) with an empty `else` branch, where the `true` branch unconditionally returns an expression containing a single self-call `fn(-x)` (`containsSelfNegCall` / `countCallsToId` == 1) and the remaining statements after the `if` contain zero self-calls (`countCallsToId` == 0). Lowers by evaluating the non-negative (`false`) continuation once for `x >= 0` and once for `-x` inside the `x < 0` branch (binding `inlineSelfSignFlipTarget := some (fnId, paramId, negResultVar)` so `fn(-x)` resolves to `negResultVar` without recursion). General recursive calls or self-calls in the non-negative continuation still fail closed (`recursive helper call <name>`). |
| Binary-search `while (low != high)` / `while (high != low)` loops with `low == 0` at loop entry and `unchecked { ... }` loop bodies (`TickLib.priceToTick`, `Env.zeroInitLocals`, `unwrapUncheckedBlockStmts`) | `Env.zeroInitLocals` tracks local variables initialized to literal `0` (`uintN low = 0;` or uninitialized default `uintN low;`) and clears membership whenever a statement can assign or mutate the local (`stmtModifiedIds`). `lowerWhile` admits `while (low != high)` and `while (high != low)` alongside `<` / `>` when `lowId ∈ env.zeroInitLocals` (failing closed with `binary-search while (low != high) requires low to be zero at loop entry` when `low` is non-zero or modified before the loop), because `0 = low <= high` and `mid = midpoint(low, high) < high` whenever `low < high`, so both `high = mid` and `low = mid + 1` preserve `low <= high` and terminate in at most `bits` iterations. Both the outer `while` body and the inner `if / else` branches unwrap `UncheckedBlock` wrappers (`unwrapUncheckedBlockStmts`) while preserving unchecked arithmetic semantics during statement lowering. |
| Three-key scalar and struct mappings (`mapping(K1 => mapping(K2 => mapping(K3 => V)))`, `SPath.two` with hashed outer pair) | `mappingSpine` accepts `1`, `2`, or `3` keys from `mappingKey` (`address` / contract / interface, `bytes32`, `int256`, `bool`, `enum`, `uint8`–`uint256`), rejecting 4+ keys (`unsupported mapping key count 4`). For 3-key mappings (`info.keyTypes.size == 3`), `lowerRef` lowers triple-indexed accesses `m[k1][k2][k3]` by hashing the outer two keys into a single synthetic first-key slot `outerHash := keccak256(abi.encode(k2, keccak256(abi.encode(k1, slot))))` (`computeNestedMappingSlot`) and routing the third key `k3` through the 2-key storage path (`SPath.two info.name (.localVar outerHash) k3Val.expr`, emitted as `FieldType.mapping2` in `importSlice`). Supports scalar reads, `=`, `delete`, compound assignments, `++` / `--`, and struct-valued 3-key mappings (including `storage` struct aliases, member reads/writes, nested struct mappings/arrays, whole-struct assignment/`delete`, and helper arguments). Partial indexing (`m[k1]` or `m[k1][k2]` on a 3-key mapping) fails closed. |
| Top-level fixed-size 1-D unsigned scalar storage arrays (`uintN[L]`, `layout.encoding == "inplace"`, `SPath.zero`) | `buildField` decodes top-level `t_array(t_uintN)L_storage` state variables (`1 <= L <= 32`) via `fixedUnsignedArrayElement?`, expanding each element `i ∈ [0, L)` into a packed or full-word `Member` `__solidity_element_<i>` (`slotOffset = (i * bits) / 256`, `packed = PackedBits` when `bits < 256`) and emitting per-element scalar fields `_verity_struct_<field>___solidity_element_<i>` in `importSlice` (`!info.fixedArrays.isEmpty`). `lowerExpr`, `lowerRef`, `lowerLocal`, `lowerCallArgs`, and `lowerEffect` support `.length` (as constant `L`), `arr[idx]` reads and `arr[idx] = val` / `delete arr[idx]` writes with `idx < L` `Panic(0x32)` bounds guards and constant-index fast paths, `uintN[L] memory snap = arr;` and `uintN[L] memory` helper arguments (`copyStorageFixedArrayToMemory`), and whole-array `delete arr` (zeroing all `L` element members). Signed or multi-dimensional top-level fixed storage arrays fail closed (`unsupported storage type ...`). |

### Development slice: `mapping` values of dynamic `string` and `bytes` (`ERC721URIStorage`), dynamic `new bytes(len)` / `new string(len)` allocations, Yul `mstore8`, `while (true)` division/shift loops (`Strings.toString` / `Strings.toHexString`), and `bytes1`–`bytes32` literal constants in Yul

| Supported Solidity | Lowering boundary |
| --- | --- |
| 1-key and 2-key `string` mappings and 2-key `bytes` mappings (`mapping(uint256 => string) private _tokenURIs`, `mapping(address => mapping(uint256 => bytes)) public scopedPayloads`) | `buildField` decodes `encoding == "bytes"` (`numberOfBytes == 32`) mapping leaf types for 1-key and 2-key `string` mappings and 2-key `bytes` mappings (`bytesStorage := true`, `stringStorage := rawLeafType == "string"`), while preserving the rejection of 1-key `mapping(K => bytes)` (`unsupported mapping value encoding bytes`). `resolveStorageBytesTarget?`, `lowerEncodedBytes`, `lowerEffect`, `lowerLocal`, `lowerCallArgs`, and `lowerPublicStateVarGetter` compute the leaf header slot via `computeSPathBaseSlot` (`keccak256(abi.encode(k, slot))` or 2-key `keccak256`) and route reads (`lowerStorageBytesRead`), length queries (`bytes(m[k]).length`, `m[k1][k2].length`), writes (`m[k] = val`, rejecting stateful/assignment RHS when the key prelude is non-empty), `delete m[k]`, `string storage` / `bytes storage` local aliases (`string storage _tokenURI = _tokenURIs[tokenId];`) and helper arguments (`_writeScopedPayload`, `StorageSlot.getBytesSlot`), and synthesized `public` mapping getters through `_verity_raw_storage`. |
| Dynamic `new bytes(len)` and `new string(len)` memory allocations in `unchecked` blocks (`Strings.toString`, `Strings.toHexString`) | In `lowerLocal` (`isNewBytesInit && (← get).unchecked`), `bytes memory buf = new bytes(len)` and `string memory buf = new string(len)` evaluate `len` as an unsigned word, guard `len <= 2^64 - 1` (`Panic(0x41)`), allocate a 32-byte length header plus `32 * ((len + 31) / 32)` zero-initialized payload bytes at `mload(64)` with `uint64` free-memory overflow guards (`Panic(0x41)`), register `(pointer := headerPtr + 32, size := len)` in `byteBuffers` / `stringBuffers`, and bind `buf` to `headerPtr` in `Env.yulNames` so inline assembly can address the ABI header at `buf` and payload bytes starting at `add(buf, 32)`. Unchecked-outside `new bytes(len)` allocations without a `ShortStrings` 32-byte assembly consumer remain rejected. |
| Yul `mstore8(addr, val)` in `InlineAssembly` and `bytes1`–`bytes32` string/hex literal constants in Yul (`Strings.HEX_DIGITS`) | `lowerYulStmtSlice` lowers `mstore8(addr, val)` to an exact read-modify-write on the containing 32-byte word (`wordAddr := addr & ~31`, `shift := 8 * (31 - (addr & 31))`, `mstore(wordAddr, (mload(wordAddr) & ~(0xff << shift)) \| ((val & 0xff) << shift))`). `index` and `bindYulExternalConstants` admit `bytes1`–`bytes32` `constant` state variables initialized with string/hex literals (`bytes16 private constant HEX_DIGITS = "0123456789abcdef"`), left-aligning the hex payload to a 256-bit word (`word * 16^(64 - hex.length)`) in `Env.yulNames` for `byte(idx, HEX_DIGITS)`. `lowerStringHelperStmts` supports multi-statement `string memory` / `bytes memory` helpers containing `UncheckedBlock`, `ForStatement`, `WhileStatement`, `InlineAssembly`, `IfStatement` (including early-return or revert branches), and `RevertStatement`. |
| Bounded `while (true)` division/right-shift loops with `if (v == 0) break;` (`Strings.toString`) and `int_const` subtraction folding (`(1 << 128) - 1` in `Math.log256`) | `lowerWhile` supports `while (true)` loops whose body contains no `return`, updates an unsigned writable local `v` (`uintN`, `bits <= 256`) only in the penultimate statement via `v /= d` / `v = v / d` (`d >= 2` literal) or `v >>= k` / `v = v >> k` (`1 <= k < 256` literal), and ends with `if (v == 0) break;` (with no other `break` or `continue`), lowering to a `doneVar`-guarded `Stmt.forEach` bounded by `bits` iterations. `lowerBinary` folds non-negative `int_const` subtractions `a - b` when `a >= b` and `a - b < 2^256`. |

### Development slice: `Strings.toHexString` (all overloads), `Strings.toStringSigned`, `Strings.equal`, `Arrays.findUpperBound`, `BitMaps.setTo`, fixed-bytes indexing (`HEX_DIGITS[idx]`), `bytes1` casts, `bytes memory` element writes (`buffer[i] = ...`), and decrementing `for` loops

| Supported Solidity | Lowering boundary |
| --- | --- |
| Fixed-bytes indexing (`b[idx]` on `bytes1`–`bytes32`, `HEX_DIGITS[value & 0xf]`) and `bytes1` casts (`bytes1("0")`, `bytes1(uint8)`, `uint8(bytes1)`, `bytes1(bytes32)`, `bytes32(bytes1)`) | `lowerRef` and `lowerExpr` admit `bytes1`–`bytes32` literal `constant` declarations (`numericConstants`) as left-aligned 256-bit words (`word * 16^(64 - hex.length)`), and lower `base[idx]` on any pure/stateless `bytes1`–`bytes32` value with an unsigned index `idx` to a `idx < W` bounds check (`Panic(0x32)`) and `Expr.shl 248 (Expr.byte idx base)` (a left-aligned `bytes1` word). `lowerCast` supports `bytes1` casts from 1-byte string/hex literals (`byteVal * 2^248`), `uint8` (`(x & 0xff) << 248`), `bytes32` / `bytes4`, and `0xXX` hex integer literals, as well as `uint8(bytes1)` (`x >> 248`) and `bytes32(bytes1)` / `bytes4(bytes1)`. Stateful or assignment fixed-bytes base/index expressions and multi-byte string literal casts to `bytes1` fail closed with located diagnostics. |
| Dynamic `bytes memory` element writes (`buffer[i] = val` / `delete buffer[i]`) and `new bytes(a + b)` allocations (`Strings.toHexString(uint256, uint256)`, `Strings.toStringSigned`) | `lowerLocal` admits `bytes memory buf = new bytes(len)` / `string memory buf = new string(len)` outside `unchecked` blocks when `len` is a binary arithmetic expression (`2 * length + 2`), checking `len` before allocating a header-backed `(pointer := headerPtr + 32, size := len)` buffer with `buf` registered in `Env.yulNames`. `lowerEffect` supports `buffer[idx] = rhs` and `delete buffer[idx]` on `new bytes(...)` buffers (`byteBuffers` with `yulNames` entry) when `idx` is a pure/stateless unsigned expression and `rhs` is a `bytes1` expression or 1-byte string/hex literal (`"0"`, `"x"`, `HEX_DIGITS[...]`), enforcing `idx < buffer.size` (`Panic(0x32)`) and performing a single-byte read-modify-write at `buffer.pointer + idx`. |
| Decrementing `for (uint256 i = start; i > lower; --i)` loops (`Strings.toHexString`) | `lowerFor` supports `for (uint256 i = start; i > lower; --i)` (and `i--` / `i -= 1`) when `i` is not modified in the loop body and `lower` is an invariant literal, parameter, or unassigned local, evaluating `start` once, computing `count := start > lower ? start - lower : 0`, and executing `Stmt.forEach iterIdx count` with `i := start - iterIdx` bound in `values` and `yulNames`. |
| `Arrays.findUpperBound(uint256[] storage, uint256)`, `BitMaps.setTo`, and `Strings.equal(string memory, string memory)` | `lowerWhile` binary-search recognition (`classifyBinarySearchBranch`) unwraps `UncheckedBlock` inside `if / else` branches (`unchecked { low = mid + 1; }` in `Arrays.findUpperBound`) and accepts helper calls (`Math.average(low, high)`) and storage dynamic array reads (`array.unsafeAccess(mid).value > element`) in the branch condition. `lowerYul` lowers `mstore(0x00, a)` / `keccak256(a, b)` in inline assembly (`Strings.equal` via `keccak256(add(a, 0x20), mload(a)) == keccak256(add(b, 0x20), mload(b))`) when `a` and `b` are header-backed `string` / `bytes` bindings in `yulNames` (`bindHelperParams` binds `string memory` / `bytes memory` parameters in `yulNames` to a materialized `[length, payload...]` header block). |

### Development slice: `ECDSA` Yul signature unpacking (`mload(signature)` / `mload(add(signature, 0x20/0x40/0x60))`), provably-bounded Yul narrow-local assignments (`v := byte(0, ...)`), custom-error scalar-cast arguments (`ECDSA._throwError`), and `StorageSlot.getStringSlot(bytes32)` / `StorageSlot.getBytesSlot(bytes32)`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Yul byte-buffer header and word loads (`mload(b)` and `mload(add(b, offset))`, `ECDSA.tryRecover(bytes32, bytes memory)`, `yulByteBufferLoad?`) | `bindRoot`, `bindHelperParams`, and `lowerLocal` record unshadowed `bytes memory` and `string memory` variables in `Env.yulMemoryStructs`. When `b` is not bound in `Env.yulNames` (`yulByteBufferByName?`), `lowerYul` lowers `mload(b)` to `{ pre := buf.pre, expr := buf.size }` and `mload(add(b, offset))` / `mload(add(offset, b))` for 32-byte-aligned positive word offsets (`offset >= 32 && offset % 32 == 0`, `yulPositiveWordOffsetLiteral?`) to `Expr.mload (.add buf.pointer (.literal (offset - 32)))`. Zero or unaligned offsets fail closed (`unsupported Yul builtin mload`). |
| Yul assignments of provably-bounded expressions to narrow non-enum scalar locals (`uint8 v; assembly { v := byte(0, mload(add(signature, 0x60))) }`, `isProvablyBoundedYulExpr`) | `lowerYulDirectAssignmentTarget` admits Yul assignments to narrow non-enum scalar locals/parameters (`bool`, `uint8`–`uint248`, `address`) when the lowered RHS expression is provably bounded by `2^bits` (`isProvablyBoundedYulExpr`: `.literal n` with `n < 2^bits`, `.byte _ _` for `bits >= 8`, `.lt`/`.gt`/`.slt`/`.sgt`/`.eq`/`.logicalNot` for `bits >= 1`, `.bitAnd` with a mask `< 2^bits`, `.shr` by `>= 256 - bits`, or `.mod` by `0 < m <= 2^bits`). Arbitrary unmasked Yul expressions (`narrow := add(narrow, 1)`, `v := mload(...)`) continue to fail closed (`Yul assignment to narrow local <name> is unsupported`). |
| Scalar `typeConversion` casts in custom-error revert arguments (`revert ECDSAInvalidSignatureLength(uint256(errorArg))`) | `lowerErrorArguments` accepts single-argument `typeConversion` calls whose inner expression is an identifier bound in `Env.values` (such as `uint256(errorArg)` where `errorArg` is `bytes32`), lowering and converting the argument via `convert errorParamType (← mType argument) (← lowerExpr argument) argument`. |
| Raw `bytes32` slot wrappers `StorageSlot.getStringSlot(bytes32 slot)` and `StorageSlot.getBytesSlot(bytes32 slot)` (`inlineStorageStructFn`) | When an internal/private/library storage-pointer helper returns a 1-member wrapper struct `struct { string value; }` or `struct { bytes value; }` via a 1-statement `r.slot := slot` assembly block (`prefixYstmts.isEmpty && sMembers.size == 1 && m0Name == "value"`), `inlineStorageStructFn` binds `slot` to a fresh local and returns `SPath.bytesSlot ("", .localVar slotBinding) isString`, enabling `.value` reads, `.value.length`, `.value = ...` writes, `delete ...value`, and `string storage` / `bytes storage` helper arguments on raw `bytes32` slots. |

### Development slice: `Create2.computeAddress`, `Clones.predictDeterministicAddress`, `keccak256(_msgData())`, and bounded `DoubleEndedQueue.Bytes32Deque` `popFront` / `popBack` `while` loops (`Governor._checkGovernance`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `Create2.computeAddress(bytes32, bytes32, address)` and `Create2.computeAddress(bytes32, bytes32)` (`lowerYulPrefixKeccakBlock?`) | Recognizes the 7-statement Yul block `let ptr := mload(0x40); mstore(add(ptr, 0x40), bytecodeHash); mstore(add(ptr, 0x20), salt); mstore(ptr, deployer); let start := add(ptr, 0x0b); mstore8(start, 0xff); addr := and(keccak256(start, 85), 0xffffffffffffffffffffffffffffffffffffffff)` and lowers it to 3 word-aligned 32-byte writes at `ptr = mload(64)` (`word0 = (prefixByte << 248) \| ((deployer & (2^160 - 1)) << 88) \| (salt >> 168)`, `word1 = (salt << 88) \| (bytecodeHash >> 168)`, `word2 = bytecodeHash << 88`) followed by `keccak256(ptr, 85)` and the target assignment. Mismatched offsets, prefix widths, or hash lengths fail closed. |
| `Clones.predictDeterministicAddress(address, bytes32, address)` and `Clones.predictDeterministicAddress(address, bytes32)` (`lowerYulPrefixKeccakBlock?`) | Recognizes the 8-statement Yul block `let ptr := mload(0x40); mstore(add(ptr, 0x38), deployer); mstore(add(ptr, 0x24), 0x5af43d82803e903d91602b57fd5bf3ff); mstore(add(ptr, 0x14), implementation); mstore(ptr, 0x3d602d80600a3d3981f3363d3d373d3d3d363d73); mstore(add(ptr, 0x58), salt); mstore(add(ptr, 0x78), keccak256(add(ptr, 0x0c), 0x37)); predicted := and(keccak256(add(ptr, 0x43), 0x55), 0xffffffffffffffffffffffffffffffffffffffff)`, packing the 55-byte EIP-1167 creation code into 2 aligned words at `ptr` and `ptr + 32`, binding `initHash := keccak256(ptr, 55)`, packing the 85-byte CREATE2 preimage into 3 aligned words at `ptr + 64`, `ptr + 96`, and `ptr + 128`, and evaluating `keccak256(ptr + 64, 85)`. |
| `keccak256(_msgData())` and zero-argument `bytes calldata` / `bytes memory` `msg.data` helpers (`lowerMsgDataBuffer`, `lowerEncodedBytes`, `lowerStringHelperStmts`) | `lowerEncodedBytes` and `lowerStringHelperStmts` accept zero-argument internal/private/public helper calls returning `bytes calldata` or `bytes memory` whose single `return` expression resolves to `msg.data` (via `inlineMsgDataFn`), materializing the full `calldatasize`-byte transaction calldata (selector word plus calldata words) into an aligned memory buffer via `lowerMsgDataBuffer` while keeping direct `keccak256(msg.data)` rejected at `msg.data`. |
| Bounded `DoubleEndedQueue.Bytes32Deque` `popFront` / `popBack` `while` loops (`while (_governanceCall.popFront() != msgDataHash) {}`, `Governor._checkGovernance`, `lowerWhile`) | `lowerWhile` recognizes `while (deque.popFront() != target) {}` and `while (deque.popBack() != target) {}` (with `popFront` / `popBack` on either side of `!=`) when `deque` resolves to a storage `Bytes32Deque` path (`struct { uint128 _begin; uint128 _end; mapping(uint128 => bytes32) _data; }`) with an empty key prelude, `target` is a pure/stateless `bytes32` expression (`!statefulCallIn target && !assignmentIn target`), and the loop body is empty (`bodyStmts.isEmpty`). Lowers to `bound := ((_end - _begin) & (2^128 - 1)) + 1`, `done := 0`, and `Stmt.forEach loopVar bound [ite (done == 0) (popPre ++ targetPre ++ [ite (popVal == targetVal) [done := 1] []]) []]`, so matching elements terminate the loop and missing elements pop until `_begin == _end` and revert with `QueueEmpty()` on the `(len + 1)`-th iteration. Non-empty loop bodies or stateful/non-`bytes32` targets fail closed with located diagnostics. |

### Development slice: `bytes calldata` / `msg.data` slices (`data[start:end]`), `Governor._isValidDescriptionForProposer` (unaligned Yul tail `mload`, `bytes` element reads, bounded tail-window `for` loops), `bytes1`–`bytes31` locals/helpers/casts (`bytes12`, `bytes20`, `ERC2771Context`), and `MemberAccess` tuple assignments (`AccessManager`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `bytes calldata` and `msg.data` / `_msgData()` slices (`data[start:end]`, `data[start:]`, `data[:end]`, `data[:]`, `lowerCalldataSlice?`) | `lowerCalldataSlice?` recognizes `IndexRangeAccess` on unshadowed `bytes calldata` parameters (`calldataBytes` with `inMemory == false`), direct `msg.data`, and zero-argument `bytes calldata` helpers returning `msg.data` (`_msgData()`). Evaluates optional unsigned `start` (default `0`) and `end` (default `base.length`) bounds once, enforces `start <= end` and `end <= base.length` (reverting with empty returndata on out-of-bounds slices, matching `solc`), and yields `(slicePre, baseOffset + start, end - start, isMsgData)`. Supported in `.length` (`MemberAccess`), `bytesN(slice)` casts (`1 <= N <= 32` via `lowerBytesToFixedBytes`, stitching the 4-byte selector word and calldata payload when `isMsgData` and `offset < 4`), `abi.decode(slice, (...))` (`lowerAbiDecodeItems`, when `!isMsgData`), and memory materialization (`lowerEncodedBytes`, copying `len` bytes into an aligned memory buffer for `bytes(slice)`, `keccak256(slice)`, `abi.encode*`, and `bytes.concat`). Signed slice bounds or `IndexRangeAccess` on `memory` / `storage` arrays fail closed. |
| `Governor._isValidDescriptionForProposer`: unaligned Yul byte-buffer tail `mload(add(buf, sub(len, k)))`, dynamic `bytes` / `bytes(string)` element reads `b[i]`, and bounded tail-window `for (uint256 i = len - K; i < len; ++i)` loops | In `yulByteBufferLoad?`, `mload(add(buf, sub(lhs, k)))` (and `mload(add(sub(lhs, k), buf))`) on a headerless `EncodedBytes` buffer (`yulByteBufferByName?`) with literal `1 <= k <= 32` computes `addr := buf.pointer + (lhs - (32 + k))` and reconstructs the unaligned 32-byte word from the two surrounding aligned words (`(mload(addr & ~31) << (8 * (addr & 31))) \| (mload((addr & ~31) + 32) >> (256 - 8 * (addr & 31)))`); `k == 0` or `k > 32` fails closed (`unsupported Yul builtin mload`). In `lowerExpr`, `IndexAccess` `b[idx]` on dynamic `bytes` (`bytes memory`, `bytes calldata`, `bytes storage`, `bytes(str)`) evaluates `buf ← lowerEncodedBytes b`, checks `idx < buf.size` (`Panic(0x32)`), and loads the single byte at `buf.pointer + idx` as a left-aligned `bytes1` word (`shl 248 (byte (addr & 31) (mload (addr & ~31)))`). `lowerFor` and `lowerHelperFrom` support `for (uint256 i = bound - K; i < bound; ++i)` (`1 <= K <= 256` literal, `bound` invariant), running `K` iterations with `i := (bound - K) + iterIdx` (including early `if (...) return ...;` inside single-return helpers). |
| Narrow fixed-bytes (`bytes1`–`bytes31`) locals, helper parameters/returns, `bytesN("...")` string literal casts (`N < 32`), and `bytes12` / `bytes20` integer/address conversions (`ERC2771Context._msgSender()`, `Votes`) | `localParamType`, `cleanHelperResultExpr`, and `lowerYulDirectAssignmentTarget` support `bytes1`–`bytes31` (`ParamType.bytesN w`, left-aligned to `256 - 8*w` bits), while keeping root ABI parameters and storage fields restricted to `bytes4` and `bytes32`. `lowerCast` supports `bytesN("...")` / `bytesN(hex"...")` for `1 <= N < 32` when the literal byte length is `<= N` (leaving `bytes32("...")` rejected), `bytesN(bytesSliceOrMemory)` (`1 <= N <= 32`), `bytes12(uint96)` / `uint96(bytes12)` (`shl 160` / `shr 160`), `bytes20(uint160)` / `uint160(bytes20)` / `bytes20(address)` / `address(bytes20)` (`shl 96` / `shr 96`), and widening/truncating conversions between `bytes12` / `bytes20` and `bytes32`. `lowerBinary` supports `==`, `!=`, `<`, `<=`, `>`, `>=`, `&`, `\|`, and `^` on matching `bytesN` types (rejecting implicit `int_const` operands), and `AbiEncoding` packs `bytes1`–`bytes32` values by their exact byte width (`scalarPackedWidth`). |
| Tuple assignment with `MemberAccess` storage or flat-struct targets (`(_roles[roleId].grantDelay, effect) = _roles[roleId].grantDelay.withUpdate(...)`, `AccessManager`) | `lowerEffect` `TupleExpression` assignment supports `MemberAccess` components alongside `Identifier` components, resolving each `MemberAccess` target against flat `memory` struct locals (`flatStructs`), ERC-7201 raw-slot storage structs (`SPath.rawSlot`), and top-level or 1-/2-/3-key mapping-backed storage structs (`SPath.zero`, `SPath.one`, `SPath.two`) with boolean `0`/`1` normalization and key-capture prelude validation. |


### CREATE2 constructor execution groundwork (not source admission)

The executable `Create2Operation` now composes value-zero caller preparation,
physical initcode slicing and both EIP-1014 hashes, nonce/collision/access gates,
the exact Midnight constructor, code-deposit accounting and canonical account,
code-size and target-storage effects. It requires an actual opcode-entry
gas/depth/static context and access set. Gas is separate from rollbackable world
state; the explicit same-caller rollback helper restores world/access snapshots
without refunding gas already spent. Unsupported entered constructor bytes fail
closed, and constructor recognition is skipped on collision/depth/nonce failure.
This operation is not yet wired into Source/Denote/IR or the importer. Full
caller gas accounting, byte-call/revert agreement and whole-function A/B/C
remain required before this becomes a Supported Solidity entry.

`Verity.Core.Model.MidnightInitcode` operationally executes Midnight's exact
`600b380380600b5f395ff3` prefix and proves that its nine instructions return
exactly the raw appended payload from fresh callee memory. This is not a
STOP-prefixed runtime convention or a substitution of a predicted address.
The proof covers every payload satisfying the initcode cap. Callee opcode and
memory gas are now computed instruction by instruction, with a universal proof
of exact return/gas remaining when sufficient and actual OOG when insufficient.
The raw prefix cost is `21 + 6*w + w*w/512`, `w = ceil(payload.size/32)`.
Caller entry/hash/initcode/forwarding and deposit accounting, rollback, source
lowering and complete A/B/C validation remain necessary before CREATE2 can enter
the Supported Solidity table.

`Create2Callee` now computes constructor outcome, runtime acceptance and code
deposit directly from the metered interpreter and forwarded gas. Its proofs
connect these computed outcomes to entered-boundary account installation,
collision, exceptional failure and account frames. This remains groundwork,
not source admission: complete caller entry/gas context, physical-initcode
recognition/addressing, canonical opcode execution and A/B/C are still needed.

`Create2NonceEntry` additionally computes the creator-nonce guard before
reservation: overflow at 2^64-1 returns zero with all accounts preserved and
all forwarded gas refunded. It rejects nonce projections beyond uint64.
The guard is not a complete CREATE2 entry implementation and admits no new
source functions.

`Create2Entry` computes caller memory/base/initcode/hash charges, EIP-150
forwarded gas and static/cap/gas/depth outcomes from an explicit opcode-entry
context. It is not a canonical CREATE2 arm and adds no source admission.

CREATE2 groundwork also includes target persistent-storage clearing on success
and the transaction-scoped target warming point. Both preserve constructor and
caller rollback distinctions, with real EVM controls. The canonical composed
opcode and source admission remain unfinished.


`Create2Operation` now composes the value-zero Midnight operation at an explicit
opcode boundary. Optional execution contexts in canonical Denote, Source and IR
states are consumed by companion boundary APIs; missing context is rejected.
Denote/Source state agreement and the IR companion's mandatory canonical-world
projection are kernel checked. This is not a Supported Solidity admission:
generic dispatcher/native backend integration and actual caller metering,
lowering, fixtures and full A/B/C campaigns remain required. No additional
Midnight function is admitted by these companions.


`CreationCaller` supplies bounded bytecode caller-prefix execution to the actual
pre-CREATE2 boundary using pinned EVMYulLean instruction/gas semantics. Nine real
EVM trace pairs match the full stack, gas and physical memory at that boundary.
This does not yet connect generic Source/Denote/IR dispatch, the native Yul backend
or Solidity lowering, and adds no Supported Solidity admission.


`CreationBytecode` connects actual caller execution to computed Midnight CREATE2
and the native next-instruction PC/stack/gas/memory. It checks canonical caller
identity/code and reads operands from the executed stack. Eight saved real-EVM
pairs and one constructor refusal calibrate this bridge. This still requires
generic Source/Denote/IR and native Yul integration, caller continuation/rollback,
source lowering and full A/B/C campaigns before any Solidity CREATE2 admission.


`CreationExecution` extends the calibrated local bytecode caller through STOP,
RETURN and REVERT with exact output bytes, gas and terminal world/access rollback.
Eight complete retained real-EVM root executions match, with the ninth unsupported
constructor precisely refused. This is bytecode companion validation, not a new
Supported Solidity row or a full imported-function A/B/C campaign.


The deep model now has a distinct value-zero `Stmt.create2`, and canonical Denote
dispatch computes its effects with explicit interpreter-error and exceptional
outcomes. The direct Yul lowering and compiler traversals build, and the Source
statement mirror preserves typed interpretation errors and exceptional frames.
The bounded local bytecode companion supplies calibrated caller metering; its
integration into generic IR/native execution remains required. The Solidity importer does not emit this statement yet, and its last
validated Midnight admission count remains 32/45. This is not a Supported
Solidity admission or a passing complete-library release gate.


The direct value-zero CREATE2 compiler arm and its validation/feature/trust
traversals now build, with a kernel-checked exact Yul-emission equation. The
IR/native execution agreement and importer family admission are still unfinished.


The Source creation dispatcher and its list/loop propagation now build, with all
116 public Source theorem audits using only allowed standard axioms. The generic
contract proof gates explicitly exclude creation until its full IR/native
execution bridge is proved; helper and raw-calldata analyses traverse all three
creation operands. Creation inside helper calls is not admitted: Option-valued
helper consumers still need typed-error propagation before that path can ship.
These checks do not increase Midnight admission or establish a release gate.


The universal Denote/Source expression, statement, list and bounded-loop
agreement now builds with typed creation failures and exceptional-frame
conversion, including a public equation for the actual creation dispatcher.
All 50 public agreement theorem audits use only allowed standard axioms.
The pre-existing conversion of Denote revert payloads to Source's plain revert
is unchanged; this proof does not establish full revert-byte agreement. Eight
Source creation boundaries match the retained real-EVM controls, plus one
precise unsupported-constructor refusal. These controls reuse saved EVM
transactions and do not validate complete imported A/B/C executions.


The differential transaction boundary now preserves precise interpretation
refusals as instrument errors. Both public Denote replay adapters reject a
populated interpretationError before emitting an EVM observation. Exceptional
frames require an actual context with zero terminal gas before they can be
observed as failed executions with empty output and whole-world rollback.
Transient storage, returndata, calls and events reset as before; the fresh
transaction also clears the physical byte-memory carrier and its word view.
Access-trace agreement and entry-point invariant assertions remain unchanged.
The read-only slice world-preservation predicate excludes interpretation errors
and exceptional exits rather than treating them as ordinary successful evidence.
This is instrument hygiene, not creation admission or a sustained A/B/C gate.


CREATE2 IR boundary update (2026-10-14): `CreationIRDispatch.dispatch` consumes already-evaluated four EVM operands, requires the actual canonical account world and matching caller address, and uses the actual opcode context and warm set. Before computing effects it synchronizes flat persistent/transient slots and physical memory from IR, preserving parked accounts and source storage channels. Typed interpretation errors and exhausted exceptional outcomes stay distinct. Six public kernel audits and eight retained EVM-boundary comparisons plus one constructor refusal validate this component; the comparisons do not replay EVM transactions. The legacy pure expression interpreter is not wired to this effectful API; helper evaluation, evaluation order, log/channel coherence, metering and native dispatch remain integration obligations. This does not expand admitted Solidity or certify full-function A/B/C agreement.


Call-aware refusal boundary (2026-10-14): `DenoteFunctionCalls` propagates interpretation errors and exceptional state through statement lists and bounded loops. Function execution and framed calls now return `Except String`, so unsupported execution cannot become a valid EVM observation; the legacy public denotation retains the precise diagnostic in `interpretationError`. Transactions record an indexed interpretation error, roll back their entry world, and do not add an observation for the refused call. Exceptional exits require actual exhausted context and preserve empty failure output and rollback. The ordinary word-return/revert interface and its separately retained `FunctionExecution.revertBytes` remain legacy interfaces; this update does not certify exact revert-byte transport across multi-contract frames. `CallRefusal.lean` verifies control propagation, exact refusal metadata, exceptional validation, atomic rollback after a successful value/storage call, and ordinary-revert distinction. Five executable component mutants are independently replayed by `scripts/solidity_differential/check_call_refusal_mutations.py`, invoked by the stateful suite and global mutation gate. These controls are not CREATE2 Solidity admission or a full A/B/C creation campaign.


Effectful IR traversal update (2026-10-14): `IRCreationInterpreter` threads actual computed creation effects through expressions, bindings, sequences and bounded control flow. Yul operands evaluate right-to-left; lexical scope keeps outer assignments and drops new locals, with shadowing and unsupported helpers/void builtins precisely refused. Evaluation-fuel exhaustion is an interpretation error, never an EVM revert. Each creation consumes a required explicit opcode-entry context; the computed post-opcode context is retained and cannot supply another creation's entry gas implicitly. Six public imported kernel audits, permanent component smoke, eight retained EVM-boundary pairs plus one constructor refusal, and six independently replayed component mutants verify this traversal. Supplied schedules still require authentication by actual native caller execution; ordinary builtin metering/memory-footprint agreement, helper/void-call integration, full-function Source/native/compiler selection and A/B/C remain open. The original pure IR APIs and assertions are unchanged. This does not admit CREATE2 Solidity or certify a sustained campaign.

Typed imported function wrappers return `Except String (Option result)`: interpretation refusal is `.error`, ordinary EVM failure is `.ok none`, and successful void calls are `.ok (some ())`. Unknown function names and unexpected successful return arity are precise errors. This access API exposes return words only; it is not a full ABI dispatcher, stateful execution receipt, or exact revert-byte interface. Differential drivers build their actual model dependencies before executable identity capture to prevent stale semantic artifacts.

Source helper calls in statement position preserve a failed helper’s interpretation diagnostic through both `internalCall` and `internalCallAssign`. Their exact public characterizations and permanent runtime/mutation checks cover this projection; ordinary helper reverts remain reverts. Expression-position helper evaluation still uses an `Option` interface and does not certify diagnostic transport. No creation-in-helper source support is admitted by this change.

`NativeCreationBoundary.run` executes the bounded local native caller prefix to CREATE2, checks every active memory byte and the four EVM-normalized IR operands, and obtains the opcode context from the executed machine. Canonical-world, caller, slot and returndata agreement are explicit proof inputs. Candidate contexts are ignored. This boundary refuses unsupported prefixes and nested creation arguments; it is not a whole-function compiler certificate, a root transaction executor, or new Solidity admission. Expression helper refusal transport and native world/ordinary-builtin agreement still require integration.

The native CREATE2 boundary has executable component mutations for using uncharged root gas, bypassing memory authentication, checking only memory size, and bypassing operands. Permanent smoke tests reject all four; single-boundary witnesses independently reproduce each mismatch. These tests do not constitute a whole-function native/compiler proof or imported A/B/C creation campaign.

The internal effectful IR creation interpreter can prepare physical constructor memory with `mstore` and `mstore8`. This does not admit Solidity CREATE2: authenticated gas/world/byte transport and whole-function lowering obligations remain. `PYTHONPATH=scripts python3 -m solidity_differential.check_ir_memory_programs --output .lake/ir-memory-programs` calibrates bounded generated memory programs with three equivalent IR and EVM variants, comparing exact bytes against DenoteMemory. Store component mutations include overlap, low-byte and offset-normalization faults; unsupported arity remains an interpretation diagnostic.

The staged effectful IR now executes whole-word `returndatacopy` and physical
`revert` with distinct byteful-revert, exceptional and refusal outcomes. A copy
bounds failure requires the actual supplied opcode context and consumes its gas;
missing context fails interpretation. REVERT captures the actual physical slice
and terminal transport preserves it through sequences and wrappers. This adds
no Supported Solidity admission: native authentication/metering, raw returndata
buffers and canonical whole-function integration remain open.

`python3 -m scripts.solidity_differential.check_returndata_programs --output PATH`
calibrates bounded programs against real EVM, typed Source and effectful IR, with
three semantically equivalent variants. The generator lives in `programs.py`.
Exceptional EVM traces are checked directly rather than passed through the
ordinary-revert observation route. Exact copied bytes, size agreement, zero
exceptional gas, touched-storage absence and event absence are checked. The
whole-word buffer is an explicit boundary; no arbitrary raw call return bytes
are projected into that representation. Seven executable component mutations
have successful baselines and independently replayed minimal divergences;
`scripts/solidity_import_mutations.py` invokes them. These are primitive
calibrations, not imported-contract or sustained whole-function A/B/C evidence.


Canonical copy integration (2026-10-14): ordinary/event-aware/helper-aware
Source and compiler-free Denote now share the exact whole-word physical copy
primitive. Operands normalize modulo 2^256. Out-of-bounds copies exhaust the
actual opcode context; missing context refuses interpretation. The permanent
CanonicalReturndataChecks fixture verifies the four consumers, bytes, frame,
normalization and precise refusal. check_returndata_programs.py additionally
compares these canonical consumers to real EVM, typed Source and staged IR.
This remains primitive calibration; legacy canonical IR result/dispatcher and
GenericInduction.Storage proofs require migration before whole-function
correspondence can be claimed. No additional Solidity function is admitted.


Canonical IR result transport (2026-10-15): ordinary/helper IR execution now
keeps exceptions and interpretation refusals distinct from byteful REVERT.
Returndata-copy operands normalize before the bounds check; a failing check
requires actual opcode context, exhausts its gas, and otherwise precisely refuses.
Helper REVERT preserves its actual captured bytes. Public function projections
retain typed metadata and roll back storage/mappings/events. The interpreter,
original scope/conservative-extension proofs and physical-memory coherence compile.
Whole-function Source/IR correspondence, true context/legal-buffer admission,
helper evaluation order and full-library integration remain open. Fresh seed214
calibration passed 36 real-EVM transactions, and eleven canonical IR mutations
were detected and independently replayed with matching current source identities.
These are component checks; this adds no Solidity function or whole-contract
certificate.


Public Source exception projection (2026-10-15): the ordinary/helper function
and constructor boundaries retain actual exceptional context separately from
REVERT bytes. The shared projection accepts only an existing context with zero
terminal gas; missing context or nonzero gas yields a precise interpretation
refusal. Arbitrary-state laws preserve storage/events rollback, and permanent
runtime checks exercise real copy bounds failure, invalid-context near misses,
public missing-context refusal and dirty terminal storage rollback. The Source
module and initial fixture/runtime checks passed. Internal-helper terminal state,
entry context admission, FunctionBody correspondence and full integration remain
open; this component change admits no additional Solidity function.

The four public Source exception mutants passed semantic detection and independent
minimal replay with current source hashes verified: actual context erasure,
nonzero-gas acceptance, missing-context coercion and terminal-storage rollback
erasure. Compile failures were rejected as infrastructure failures. This targeted
receipt does not establish the full global mutation gate or contract equivalence.


FunctionBody canonical transport (2026-10-15): statement-to-public exception
projection now uses the same Source rule, and ordinary/helper IR result projections
preserve exceptional context and refusal messages separately from REVERT bytes.
Six terminal-if proof paths use bounded generic suffix/block transport lemmas;
original theorem conclusions and existing certification relations are unchanged.
FunctionBody and GenericInduction.ResultRelation compiled together (1246 jobs).
This establishes migration compatibility for their existing supported proof
fragments, not the remaining Storage or whole-contract correspondence obligations.


Runtime-context alignment migration (2026-10-15, integration in progress): both
runtime/constructor alignment predicates now require equality of the actual Source
and IR execution contexts. The Base module compiled with this stronger invariant,
including physical-copy preservation. Operational generic step relations distinguish
exception and refusal, while public certification still excludes refusals. The
bounded copy proof is being migrated to normalized operands and exact typed exits;
Storage and its consumers are not yet verified. In particular, operational-to-
certified helper transport requires explicit no-refusal admission, and returndata
bubbling still requires proof of the actual retained-buffer extent.


Retained-buffer admission (2026-10-15, build pending): runtime/constructor
alignment now explicitly requires the actual retained byte extent to fit the EVM
size word. This is necessary to prove full-payload bubbling rather than a
truncated-size REVERT; it is not inferred for arbitrary lists. The old bubbling
proof body has been replaced by the exact physical payload theorem. Frame entry
really resets the buffer, while future buffer-installation/native-oracle admission
must establish and preserve the size bound. No supported syntax was removed and
no byte relation relaxed. The strengthened invariant and all consuming proof
chains still require successful integration checks.


Storage proof integration verified (2026-10-15): GenericInduction.Storage compiled
successfully (1254 jobs) with actual opcode-context equality and retained-buffer
extent admission. The normalized bounded-copy proof covers exact physical copies,
actual-context gas0 exceptions and precise missing-context refusals. Bubbling now
uses the full-payload theorem, preserving exact revert bytes for arbitrary admitted
payload words. GenericReturndataChecks compiled (1256 jobs), including rejection
of different contexts, unrepresentable retained sizes, and exception/refusal-to-
REVERT conflation. Four audited context/extent/copy/bubbling laws depend only on
propext, Classical.choice and Quot.sound. Generic helper/public certification and
full Contracts integration remain separate pending obligations; this does not
establish imported-contract coverage or a sustained A/B/C campaign.


Operational versus certified transport (2026-10-15, helper integration pending):
generic execution results now have an explicitly named operational relation which
can transport matching precise refusals and actual exceptional states. The public
EVM certification predicate retains its no-refusal and exact REVERT-byte checks.
A kernel theorem proves that matching operational refusals cannot establish that
public certificate, with a permanent fixture consumer. Generic execution theorem
conclusions are being migrated to operational outcomes; downstream whole-function
proofs must establish their actual admission before certification. This is not a
new EVM certificate or completion of helper/public integration.

Require payload admission (2026-10-15): generic compile-core, terminal-core,
supported-list and helper-free step conversions now carry explicit
`requirePayloadsFit` witnesses. Bounds are decomposed over actual append, tail
and nested child lists; no bound is inferred for an arbitrary Lean string.
`GenericInduction.Helpers` builds with this admission and typed operational
outcomes. Whole-function certification still needs separate outcome admission;
the successful helper module build is not a complete Contracts or release gate.

Internal exception carrier (2026-10-15): Source `InternalFunctionResult` now
retains an actual terminal `RuntimeState` separately from REVERT bytes.
`failedInternalOutcome` preserves that exception and gives instrument refusal
precedence; ordinary reverts retain exact bytes. Helper exception projection
rolls back its result world while retaining the terminal carrier for the public
boundary, which still requires an actual exhausted opcode context. The Source
module and permanent component fixture build. Actual context propagation into
nested helper execution, public/native entry admission, and whole-function
certification remain open; the carrier fixture does not prove those paths.

The internal-carrier mutation campaign passed all four semantic mutants with
independent minimal replay (state erasure, exception-to-REVERT, rollback erasure,
and refusal erasure). The five carrier laws audit with `propext` only or no
axioms. This evidence is limited to the component and preserves the outstanding
nested-context/public-entry/whole-function obligations above.

Actual helper opcode context (2026-10-15): helper source entry accepts the
caller's actual optional `ExecutionContext`, initializes the callee with it,
and preserves the successful terminal context in `InternalFunctionResult`.
Void and assigning calls restore that returned context alongside the world;
caller bindings remain scoped to the caller. Registered runtime tests cover
actual direct and nested out-of-bounds copies, gas-zero/depth preservation,
contextless refusal, and successful void/assign calls. Summary soundness now
quantifies over actual contexts instead of silently covering only `none`.
The legacy expression evaluator still has an Option-only result boundary;
full typed expression admission, external-oracle/index propagation, public/native
entry admission and downstream helper/body certification remain unfinished.

The actual-context component passed seven production-definition semantic
mutants, each compiled and detected with independent minimal replay: helper
entry, void/assign call entry, successful result context, void/assign resume,
and exceptional terminal propagation. Six Source helper equations audit with
only standard Lean axioms. These results do not certify the contextless legacy
helper-body correspondence bridge or the remaining public/native/expression
admission boundaries.


Helper-body context migration (2026-10-15): the selector-aware helper-body
runtime and binding-projection seam now retain the same actual optional opcode
context as Source helper entry, and initialize error definitions from the real
`spec.errors`. The operational helper-body theorem preserves every typed outcome;
its ordinary-certification sibling separately requires proof that the actual
source execution has an ordinary outcome. That premise is not inferred from
matching refusals or exceptions. The IR body-to-call projection retains the
callee's captured REVERT memory and actual exceptional state, restoring only
caller locals; void/assign wrappers propagate refusals explicitly.

`InternalHelperSummaryContract.post` does not expose opcode context. Accordingly,
the canonical `exactInternalHelperSummary` is now the projection of contextual
execution: an existential context witness with exact success, return value and
world equalities, rather than an equality to the contextless run. This changes
the summary abstraction, not the unchanged public certification relation.
World-preservation-on-success is proved for every contextual witness, including
real error definitions; failures do not discharge a successful-world premise.
The contextual body/call bridges, summary evidence and registered
`HelperBodyContextChecks` compile. The fixture executes a declared custom error
against independently fixed selector/argument bytes, actual bounded-copy
exception/refusal cases, and terminal IR payload/local-frame preservation.
Full consumer integration, actual public/native entry admission, external oracle
and index propagation, typed expression outcomes and whole-function certification
remain open. No new Solidity family or sustained A/B/C campaign is certified here.

The helper-body bridge component passed five actual-definition semantic mutations
(error-table erasure, context erasure, REVERT-terminal erasure, exception-to-REVERT,
and refusal-to-REVERT). Every mutant compiled, failed the permanent runtime
semantically, and produced a distinct independent minimal witness with an identical
replay. Source, fixture, runner and clone hashes were checked against the receipt.
All eleven audited body/call/summary laws use only standard Lean axioms. The global
mutation gate and full exact-head merge gates have not passed on this worktree.


Helper receipt-schedule integration (2026-10-15, validation in progress): the
legacy Source helper executor now forwards the caller's actual external-call
oracle and receipt index at expression/void/assign entry. Successful results
carry the terminal receipt index; void/assign success resumes there while
retaining the caller's oracle and local bindings. Source summary soundness
quantifies over supplied contexts, oracles and starting indices. Selector-aware
source helper interpretation accepts these same inputs, and the context-hidden
canonical summary existentially projects them with exact success/return/world
relations. This does not replace typed expression integration: the legacy Option
value projection still cannot carry expression effects, refusals or exceptions.
The binding projection, body execution context and body/call proof APIs carry
the same explicitly supplied oracle and cursor; legacy callers that omit them
still select their default empty schedule. A supplied schedule is not evidence
of whole external-call agreement or authentication by native caller execution. Component Source tests cover nonzero starting indices,
nested success, continue/stop result projection, caught external failure with
rollback/returndata, scoped helper locals and caller continuation. Full required
campaigns and exact-head merge evidence remain outstanding.

The receipt-schedule component passed eleven actual-definition mutants, each
compiled, semantically detected, independently minimized and replayed. The seven
context and five helper-body mutants also pass on the changed current inputs;
all source/fixture/runner and clone hashes were independently checked. Current
contextual body/call/summary proofs and registered runtime fixtures pass, and
eight Source plus eleven body/call laws audit with standard Lean axioms only.
These are component receipts from a dirty worktree, not exact-head merge gates.


Typed external argument integration (2026-10-15): the staged typed statement
executor evaluates `externalCallBind`, `tryExternalCallBind` and `ecm` arguments
through its recursive typed expression executor, then passes the resolved
literal arguments and the actual resulting state to the existing abstract
Source call transition. Effectful helper arguments can therefore consume
receipts before the enclosing call; caught failure rolls back only that call's
proposed world, retaining argument effects and advancing the cursor. Registered
runtime checks cover direct calls, caught calls and ECMs with a nonzero initial
cursor, caller continuation, scoped locals and refusal before an enclosing call.
This does not authenticate receipt arguments or external names, expand the
whole-word receipt carrier to arbitrary bytes, establish native/public context
admission, or integrate the staged executor into canonical whole-function
certification. The five generic ordinary-certification gaps and full exact-head
validation obligations remain open. No additional Solidity construct admission
or Midnight coverage increase is claimed by this component.


Public Source context forwarding (2026-10-15): `interpretFunction`,
`interpretConstructor`, `interpretContract` and their helper-aware siblings now
accept an optional execution context and external receipt cursor. Dispatch
forwards the same oracle/context/cursor; body entry stores those actual values.
Omitted inputs retain the legacy missing-context/zero-cursor behavior rather
than inventing executable gas. Registered tests exercise all six entry routes,
including dirty-storage rollback on an actual bounds exception, exhausted
terminal gas with retained depth, refusal when context is absent, and oracle
receipt selection from index3. Six public transport/exception laws compile.
This is explicit-input transport, not native authentication: the caller still
has to establish that supplied context belongs to the modeled opcode boundary.
Whole-function gas accounting, native receipt authentication, typed canonical
execution and ordinary-versus-exceptional certification remain incomplete.
All eighteen actual-definition public-entry mutants passed semantic detection,
independent minimal witnesses and replay; the current source identities and all
73 clone hashes were verified. The six public transport laws audit with only
standard Lean axioms. No whole-contract or exact-head gate is established by
these component checks.


Contextual generic admission (2026-10-15):
`GenericInduction.ContextualBody.contextual_public_body_outcome` links the actual
public Source function, its actual body execution and compiled IR at the same
supplied oracle/context/cursor. Its operational result preserves refusal and
exception classes. `OrdinarySourceTrace` separately records actual head-step
equations, follows each real continuation state, and admits ordinary terminal
results without demanding unreachable suffix execution. Its ordinary-result
law derives the existing certificate; neither exception nor interpreter refusal
has a trace constructor. The returndata-copy rule requires the actual normalized
source/size extent to fit the retained buffer and checks the suffix at the
post-copy world. A concrete empty-buffer, zero-length, source-offset1 near miss
is proved inadmissible without context. `contextual_public_body_certified` uses
this trace explicitly. `OrdinaryHelperTrace` now supplies the analogous actual
helper-execution admission. The generic Main APIs and DenoteSound/storage
wrappers require explicit traces rather than converting arbitrary operational
agreement into an ordinary certificate. `SupportedOrdinary` derives ordinary
execution for the full `SupportedStmtList` grammar, including actual continued
append states and the normalized zero-source/zero-size copy. Its helper trace
transport uses the proved conservative extension and an event-free catalog.
Integration into Function consumers and broader event/helper domains remains
unfinished. These
Source-domain laws do not authenticate native contexts or establish opcode gas
and memory admission for a full EVM execution.

Helper error-frame preservation (2026-10-15): actual helper execution initializes
`spec.errors`. Helper statement/list preservation therefore requires the real
input alignment `state.errors = spec.errors`; a mutual, fuel-decreasing proof
establishes that actual exceptional internal-function results retain this table.
No arbitrary `InternalFunctionResult` is assumed to preserve errors. Public
function-entry and aligned continuation claims retain their original conclusions.
IR helper dispatch and fuel projections preserve exceptional contexts and
interpreter-refusal messages separately from physical REVERT data.

Public body-result integration (development, 2026-10-15): `PublicResultBridge`
packages the actual public Source entry and helper body at the supplied
context/oracle/cursor and the model's error table. Its ordinary-result theorem
uses the unchanged certificate; exceptions/refusals cannot obtain it. The Function module, including concrete supported function and constructor
packaging, compiled successfully before the subsequent dispatcher correction;
its rebuild against that correction now passes, including DispatchGeneric,
Dispatch, Contract and concrete ContractFeatureTest consumers. Physical require payload bounds were
not implied by the old unbounded message grammar. Production function validation
now walks every canonical child list and rejects overflow; the importer checks
both require strings and revert strings with source locations. The corresponding
validation-to-bound and structural fuel proofs passed focused compilation and
axiom audits. Seven finite validator mutants and thirty source admission controls
passed on their recorded identities. Both actual importer guard mutants now
also compile and are detected with independent minimal source-located replay;
their input/artifact hashes were verified before later proof refactoring.
Generated A/B/C boundary cases and all exact-head gates remain pending.


Constructor payload admission (2026-10-15, focused integration validated): production
`validateConstructorSpec` now checks exact Error(string) extent before running
its complete pre-existing checks, as `validateFunctionSpec` does. A successful
production validation supplies the bound; arbitrary raw constructor-body
compilation does not. The unchanged result predicate additionally requires an
actual ordinary execution trace, now derived from SupportedStmtList. Function and the registered constructor/require fixtures compiled, the finite
validation fixture ran successfully, and the production-success bound and
function/constructor packaging laws passed axiom audits with standard Lean
axioms only. Concrete ContractFeatureTest callers and the subsequent dispatcher rebuild
now pass too. Six guard payload mutations were detected and independently
replayed; the current eighteen-law combined dispatcher/function/constructor
audits depend only on standard Lean axioms. This is not a full Contracts or
whole-contract real-EVM validation result.


Bounded proof integration (2026-10-15): the focused production build passes
Function, physical legacy-payload checks, scalar/conditional custom-error
contracts and guard splicing. ABI loading, payload execution and public rollback
compose through shared lemmas with actual compiler receipts and fuel equations.
The original proof-length check passes without new exceptions; eighteen focused
laws use only standard Lean axioms. This does not establish full Contracts or
sustained Midnight validation. The generated padding-boundary phase completed
84 variants / 1,596 A/B/C cases without divergence, including all UTF-8 ABI
padding boundaries. Independent calldata-based checks confirmed 621 exact
guard-failure payloads. The combined runner then failed before its first
memory child because its Python module path was missing. After repairing that
launch environment, only the six missing manual memory variants were run:
72 stateful transactions agreed, including complete discovery/replay and
metamorphic observations. These separate receipts retain their respective
source identities; they are not an exact-head release gate or whole-Midnight
validation. The full Contracts integration build remains pending.


Public exception integration (2026-10-15): Denote retains an actual exhausted
opcode context separately from ordinary REVERT bytes, and rolls back public
storage/events. Missing or nonexhausted contexts remain interpreter refusals.
The event-free public Source agreement theorem compiles with its original
statement. The runtime fixture and five semantic mutations pass; this does not
admit CREATE2 or supply the unfinished native whole-function context boundary.
Full Contracts and exact-head release gates remain separate requirements.


Native-world boundary component: `NativeCreationWorld` reads actual EVMYulLean
account presence, nonce/balance/code, current/original persistent storage,
transient storage, per-account/per-slot warmth and raw event-time logs. Its
`Agreement` is an explicit canonical/native-world proof obligation; local frame
lemmas preserve it under gas/PC/stack/memory changes. The permanent
`NativeCreationWorldChecks` fixture tests these views and executes five native
`EVM.X` static-write/stipend cases calibrated against real-EVM references.
Seven semantic mutations with minimal independent witnesses exercise the actual
production definitions through `check_native_world_mutations` and the standard
mutation command. This component does not synchronize a world, authenticate a
world-changing caller prefix or admit Solidity CREATE2. Preservation through
actual storage/log/environment steps, creation-world propagation and native
resynchronization after creation remain required before admission.


`CreationCaller.checkedStep` now retains the static-write prohibition and
SSTORE stipend check needed before world-sensitive execution can be connected.
The ordinary caller runner still rejects storage/log prefixes. Direct fixture
checks compare these gates with pinned `EVM.X` and saved real-EVM outcomes;
static bypass and the exact2300gas off-by-one are exercised by
`check_native_caller_world_gate_mutations`. These guards alone do not establish
native/canonical world preservation and do not expand Solidity admission.


`NativeCreationWorldSteps` proves frame and account-map update laws for the
actual pinned native `State.sstore` and `State.tstore` primitives. SSTORE retains
original transaction storage, execution environment, existing raw logs and
account warmth; TSTORE retains the complete substate. Account updates require an
explicit presence hypothesis. Runtime checks exercise both primitives and
separate current/original/transient slots and preserved account metadata. These
laws still require composition with opcode prechecks and canonical/source-world
agreement before a world-sensitive caller prefix can be accepted.


`NativeCreationWorldWrites` proves exact self-account lookup, read-after-write
and distinct-slot frame laws for both persistent and transient native storage.
Zero-valued writes use the pinned finite-map erasure semantics while reading as
zero. The proof reuses StateBridge's established UInt256 comparison law; it adds
no assumed comparator behavior. The fixture checks zero erasure, untouched
neighbor slots and continued rejection of world-changing caller prefixes.
These native laws still need composition with canonical source storage channels
and the full checked executor before source CREATE2 can be admitted.

`NativeCreationFlatStorage` proves persistent and transient flat-slot agreement
after actual native account updates, universally over native word addresses,
including zero-erasure and distinct-slot preservation. It does not establish
source hashed-channel agreement, checked-instruction gas/refunds, raw event
decoding, creation propagation or post-creation account synchronization. The
CREATE2 caller whitelist remains unchanged.

`NativeCreationStorageAgreement` proves preservation of all twelve fields of
`NativeCreationWorld.Agreement` through actual SSTORE/TSTORE state effects,
under explicit existing-account and initial-agreement premises. This includes
foreign accounts, creation metadata, the other storage channel and account
warmth. It does not certify checked opcode execution, refunds, source hashed
channels, log decoding, CREATE2 world propagation or postcreation native
synchronization. The caller opcode whitelist remains unchanged.

The native word-order proof and single TransCmp instance now live in
`Compiler.Proofs.EvmYulUInt256Order`, shared by the native backend and IR
boundary proofs. Backend compatibility names are retained; IR proofs no longer
import the native backend state bridge. No ordering axiom was added.

`NativeCreationStorageOpcodes` connects raw boundary Agreement to actual
native SSTORE/TSTORE steps, including gas/stack/PC bookkeeping, and to every
successful `CreationCaller.checkedStep` storage execution. Exceptional guards
remain unchanged, including static writes and the post-memory-charge stipend
sentry. Real fixtures compare nontrivial writes with native `EVM.X`. Source
hashed channels, refunds, log decoding, prefix propagation and creation-world
synchronization remain separate obligations; no importer admission is enabled.

`NativeCreationLocalFrames` proves entire native State preservation for every
operation in the unchanged local caller whitelist, its successful checked
steps, and any bounded caller prefix that actually reaches CREATE2. Raw
Agreement is transported from the initial machine to that executed boundary.
This covers native accounts, original storage, substate and environment, but
does not establish source hashed-channel agreement or world-changing prefixes.
Storage/log opcodes remain excluded from the caller runner; creation-world
propagation, postcreation synchronization and full-function certification remain
unfinished. Fuel and exceptional outcomes are not successful boundaries.


`NativeCreationWorldCaller` pairs the actual checked native caller prefix with canonical flat persistent/transient writes, checking account presence. Its three public laws preserve the existing twelve-field raw Agreement through successful advances and bounded execution to CREATE2. The paired fixture calibrates a saved real-EVM persistent-write prefix and tests transient channel separation, absent-account refusal and static failure. Source hashed storage channels, decoded events, refund adequacy, rollback and postcreation account synchronization remain separate obligations; this component does not establish whole-function equivalence or expand Solidity admission.


`NativeCreationWorldExecution` forwards the computed paired prefix frame into `CreationBytecode.execReady`; its delegation law forbids substituting the entry world. The persistent-write fixture matches the saved real-EVM CREATE2 address, remaining gas and retained caller storage. Prefix execution failures and interpretation refusals remain distinct. Exceptional component frames retain the executed prefix effects; root transaction rollback is a separate obligation. Native account metadata is not yet synchronized after creation, so this composition alone cannot authenticate subsequent account-observing instructions or whole-function equivalence.


`NativeInitcodeFrames` extends the primitive whole-native-State frame to any
positive interpreter fuel and includes RETURN/STOP. `MidnightHeaderDecode`
proves that native opcode decoding anywhere below offset11 of Midnight's exact
header is independent of the appended payload, and that an actual successful
step there preserves native account/substate/environment State. The immediate
byte0x0b is included and decodes as local SIGNEXTEND. `MidnightHeaderProgress`
proves code/PC invariant preservation and strict decrease of the byte-distance
rank for every actual successful nonreturning header step, for arbitrary fuel.
`NativeMidnightConstructor` composes these laws with the actual native X
precheck/step decomposition: every successful header run preserves the entire
native State, and fuel≥13 excludes interpreter OutOfFuel for any header state,
with identical full outcomes at all larger fuel bounds. Real EVM gas and stack
exceptions remain possible. Symbolic native whole-run gas correspondence and
Lambda account commits remain separate obligations. No new
Solidity construct is admitted. The native fixture runs six arbitrary payloads
(including world-changing opcode bytes) at four sufficient fuel bounds,
compares actual output/gas with the canonical metered constructor, checks
persistent/original/transient/account channels, and rejects insufficient fuel. It also tests gas0, cost−1, cost and cost+1.


`NativeMidnightConstructorData` collects the native CODECOPY and stack-step
laws, the arbitrary-payload offset-11 write/readback theorem (including an
empty payload and preexisting memory), and local native/canonical gas
arithmetic. The native read length and word-modulus bounds remain explicit.
`NativeConstructorDataRun` now discharges the concrete header stack/memory
premises of `X_output_of_invariant`. Its `success_output` theorem proves that
any successful actual native X execution, starting at PC zero with an empty
stack and the exact constructor code, returns the appended payload. The
explicit payload-size bound is less than 2^64; initial memory is arbitrary.
The proof follows the actual decoder (including both PUSH1 immediates), all
nine reachable instruction stages, native CODECOPY and native RETURN. It
introduces no Solidity admission. Whole-run gas correspondence, wrapper fuel
transport, Lambda commits and postcreation account agreement remain separate
obligations.


`NativeConstructorXi` connects these constructor results to the actual native
Ξ wrapper and its exact initial state. Ξ consumes one fuel unit before X:
fuel at least 14 excludes interpreter exhaustion and makes its full outcome
fuel-independent for the exact header. On success its actual account map,
created-account set and substate equal their inputs, and its output is the
payload under the explicit length bound. These are kernel proofs; remaining
gas is not constrained by the wrapper theorem. The native fixture also runs
Ξ on the same six payloads at three successful fuel bounds, checks the world
and canonical gas/output, and rejects six underfuel cases. Lambda/CREATE2 fuel
transport and postcreation account commit correspondence remain unproved.


`NativeConstructorLambda` transports the constructor fuel results through the
actual pinned Lambda implementation for CREATE2. At a target with zero nonce
and empty code, computed by the exact native FFI hash expression, Lambda fuel
at least 15 excludes interpreter exhaustion and gives identical full outcomes
at larger bounds. Storage-only targets are included in this collision-free
case. The fixture executes actual Lambda for six payloads at three sufficient
bounds and six underfuel cases; it checks target storage reset, code deposit,
endowment balances, sender storage, target warmth and exact gas. This runtime
calibration is not a symbolic account-commit or whole-run gas proof. Collision
cases and the final CREATE2-step fuel transport still require separate proofs.


`NativeConstructorGasRun.success_gas` proves the exact canonical gas debit for
any successful actual native X constructor execution with initial PC zero,
empty stack and zero active-memory words, and payload size at most 49152.
Specifically, remaining gas plus `prefixCost payload.size` equals initial gas
as natural numbers. Each real Z memory/instruction guard justifies nonwrapping
subtraction; a reachable-stage invariant carries the actual stack, copied
memory, extent and cumulative debit. The local costs telescope through a
generic checked-step X invariant theorem. This conditional success theorem
does not yet prove existence of success for every sufficient-gas input or
classify every failing run. Lambda code-deposit gas, final CREATE2 fuel and
postcreation account synchronization remain separate obligations.


`NativeConstructorSuccess.run_success` completes the sufficient-gas direction
for the actual native X constructor: exact code, PC zero, empty stack, zero
active-memory words, payload size at most 49152, gas at least `prefixCost`, and
fuel at least 10 imply success. The actual output is the payload, remaining gas
is initial gas minus `prefixCost`, and the entire native State is unchanged.
The proof establishes every real opcode/stack/static/jump guard at the nine
reachable boundaries, then proves both gas gates and each actual primitive
step. It does not assume an execution outcome.

`NativeConstructorOutcome` classifies all actual X runs with fuel at least 10:
they either return the payload or fail with exactly `OutOfGass`; gas below
`prefixCost` gives precisely that exception. `NativeConstructorXiResult.xi_constructor`
transports this classification through the actual native Ξ wrapper with fuel
at least 11, including exact remaining gas and unchanged supplied account map,
created-account set and substate on success. Lambda code-deposit commit
correspondence and caller resynchronization remain separate obligations; these
theorems alone admit no Solidity CREATE2.


`NativeConstructorLambdaResult.lambda_constructor` gives the exact actual native
Lambda result for collision-free targets, payload size at most 49152 and fuel
at least 12, for all gas values. It includes native reservation, sender balance
debit, code installation or account rollback, and the actual deposit/runtime
guards. `NativeConstructorRuntimeGuard` proves the size/0xef acceptance guard
and prefix-plus-deposit budget agree with their canonical predicates, including
empty code and UInt256 non-wrapping remaining gas. Collision handling, account
map synchronization and the caller CREATE2 step remain separate obligations.

The permanent native constructor boundary fixture executes 216 actual Lambda
calls against canonical callee gas/runtime classification, including empty
code, 0xef rejection, 24576/24577-byte runtime limits, constructor/deposit gas
boundaries and both nonce/code collisions. It checks account balances, nonces,
code, persistent/transient storage, gas, logs and created/access bookkeeping
at native fuel 12 and 16. These fixture observations do not replace the
remaining symbolic collision and account-map correspondence proofs.

`NativeConstructorCollision.lambda_collision` proves the exact native Lambda
rollback for either nonce/code collision, arbitrary initialization code and
arbitrary gas, with fuel at least 3. It derives the actual invalid-code
exception through native X and Ξ; only `OutOfGass` or `InvalidInstruction`
can occur. The account map and created-account set are restored unchanged,
gas is zero, return bytes are empty, and the native target remains accessed.
This does not yet establish caller CREATE2 equivalence or world synchronization.

`NativeConstructorLambdaAdequacy.lambda_all_targets_completed` proves that
actual native Lambda with Midnight constructor code, payload at most 49152
bytes and fuel at least 12 always returns an `.ok` result for every target and
gas value. Creation failure is represented in that result; neither interpreter
exhaustion nor another exception reaches CREATE2's error-swallowing branch.
The caller still needs exact memory/code identification, its own entry guards
and account/world correspondence; this theorem alone admits no Solidity.

`NativeConstructorCreate2Fuel.create2_step_fuel_stable` proves equality of
actual native CREATE2 steps for any two fuel values at least 13, assuming
the actual stack pop and memory slice identify the supported constructor
with payload at most 49152 bytes. It retains the native entry guards and
account transformations. This is fuel independence, not yet canonical
whole-step or imported-function equivalence.

The permanent native CREATE2 fuel fixture executes 216 actual EVM.step calls
at fuel 13 and 17. It compares gas/result/account observations against the
canonical callee with actual EIP-150 forwarding and covers gas, deposit, runtime
size/0xef and nonce/code collision boundaries. It checks the creator nonce
increment and preservation of original storage, memory and transient storage.
These are component fixtures, not full imported-function differential evidence.

`NativeConstructorAccountFrames` proves actual Lambda preserves every account
outside its sender and native target, including presence/absence as well as
all account fields. The result holds for every gas value and target outcome,
with the supported constructor/payload bound and fuel at least 12. Ordering
distinctness is explicit; no absent account is substituted by a zero account.
Creator/target correspondence and whole postcreation world agreement remain.

`NativeConstructorAccountEffects` identifies the native result flag with
account installation/rollback and proves the exact target/sender record updates
when the creator exists. `NativeConstructorCompletionGuard` equates native
post-constructor runtime/deposit rejection and remaining gas with the canonical
combined predicates. `NativeConstructorVacancy` aligns the actual optional
account collision check with entry nonce/code vacancy, preserving absence.
These laws still require composition with the actual Lambda and caller result
to establish canonical whole-step and full-world correspondence.

`NativeConstructorCanonicalSuccess.lambda_result_canonical_success` identifies
the computed native Lambda result formula success flag with canonical runtime
acceptance and the complete prefix-plus-deposit budget, for a collision-free
target. It covers low gas and runtime/deposit failures without assuming success.
Exact remaining gas and account/world correspondence must still be composed
into the complete native/canonical caller result.

`NativeConstructorCanonicalGas` proves the computed native result formula gas
is exactly the canonical combined debit on success and zero on failure. Its
callee theorem identifies canonical execution with the native status, runtime
and gas for every input gas, under explicit vacancy and no-wrap premises.
These observations must still be transported through actual Lambda and
combined with account-map/world correspondence.

`NativeConstructorLambdaCallee.lambda_canonical_callee` derives a completed
result of actual pinned Lambda and its canonical callee status/runtime/gas
equality, with empty native return bytes, for every gas value under supported
payload, fuel and target-vacancy premises. No child outcome is supplied by the
caller. Creator/target canonical account and full-world correspondence remain.

`NativeConstructorLambdaAccounts.lambda_accounts` derives an actual native
Lambda result and equates its entire account map to reservation plus code
installation on success, or the original map on failure. It covers all target
conditions and gas values under the supported constructor/fuel premises. The
canonical account projection and full postcreation world agreement remain.

The native constructor zero-endowment reservation lemmas preserve the entire sender account outside the target and establish nonce one, unchanged balance, fresh persistent storage and retained code/transient storage at a vacant target. These are reservation effects, not yet whole-function native execution equivalence.

The checked native zero-value reservation projection now covers every real EVM address, including the sender: only the target account view changes, to nonce one with its balance and code retained. The actual native map also clears target persistent storage. Linking this projection to canonical creator-nonce reservation and the complete post-creation world remains required.

Native constructor reservation is now connected to canonical `Create2Accounts.reserve` under explicit account-view agreement after the creator nonce bump and native target vacancy. Actual native runtime code insertion also projects to `Create2Runtime.installRuntime` at each real EVM address. These lemmas do not assume whole-function equivalence or yet establish the complete post-creation storage world.

Actual native Lambda now derives a completed result whose own success flag selects the canonical reserved-plus-runtime account projection or rollback to the already-bumped creator map. The theorem retains explicit present-creator, vacant-target and bumped-entry agreement premises and covers every real address and every gas budget. Canonical completion and full storage-world agreement remain separate obligations.

`lambda_canonical_entered` now derives agreement between actual pinned Lambda and canonical `Create2Callee.runEntered` for vacant targets: actual success/failure, remaining gas, empty return bytes and every real account view, under the explicit present-creator/bumped-entry agreement premises. It composes actual completion and native map effects; complete storage-world agreement and whole-function importer admission remain unproved.

The actual completed native Lambda now has checked persistent/transient storage-map effects: with a present creator and zero target nonce, its own success flag clears only target persistent storage; every transient map is retained. Code-collision and gas failures roll back these effects. The theorem derives the real Lambda result and covers all real addresses, rather than assuming a selected child outcome.

Checked native storage-word projection lemmas now connect exact persistent/transient map effects to canonical `CreationStorage.clear`: target persistent words reset, foreign persistent words and all transient words survive, and the caller plain store is retained under explicit target/caller distinctness. They require the actual map effects and prior raw world agreement; they do not assume or establish full source typed-channel agreement.

Native constructor target warming projects exactly to canonical account warming at each real address, while every other substate field is retained. Successful canonical reservation also proves target/creator distinctness; this discharges, rather than hides, the corresponding caller-storage preservation premise. Full native CREATE2 world composition remains required.

The zero-value native constructor map commit now has whole-account, code and balance projection laws: only a committed target receives nonce one, fresh persistent storage and payload code; every balance is preserved, including an existing target balance. These structural effects still require composition with actual native completion before claiming full execution agreement.

Raw native world agreement now composes all existing `NativeCreationWorld.Agreement` fields after zero-value constructor map, environment and warming effects. Its canonical field update is proved equal to existing `CreationStorage.commit` when successful code installation is established. Actual Lambda/caller execution must instantiate these premises; source typed channels and whole-function equivalence remain separate.

`lambda_world_transport` now derives actual native Lambda completion and transports every raw agreement field to any real parent continuation with that result account map/substate and retained environment. Its canonical outcome commits through existing `CreationStorage.commit`; creator/target distinctness is derived from successful reservation. Premises remain present creator, vacant target, bounded Midnight payload, enough interpreter fuel, and prior raw/bumped-entry agreement. Actual CREATE2 caller-step transport, collision-world transport and source typed-channel authentication remain required.

The native CREATE2 creator nonce insertion now projects to canonical `bumpCreator` at every real address, under an explicit no-wrap bound. This establishes the account projection at child entry; raw storage-world preservation and the actual checked caller step still require composition.

The native creator nonce insertion now preserves the complete raw world relation when the canonical creation-account view is bumped consistently. Native nonce-guard legality derives the no-wrap bound, and the actual insertion proves creator presence at child entry. Code, balances and both entire storage maps are retained; source typed channels and actual CREATE2 caller-step completion are still separate obligations.

Actual native CREATE2 step frames now transport a completed real Lambda result into the parent account map, substate and created-account set, retaining parent environment, original transaction storage and physical memory. The statement keeps native entry guards and successful parent completion explicit; it does not assume a fabricated child evaluator. The native 49152-byte initcode guard implies a 49141-byte payload bound for this 11-byte constructor header.

The exact native CREATE2 child invocation is now proved to complete for the supported constructor at adequate fuel, for all target states and gas budgets. The parent frame theorem derives this real child result rather than assuming a completion certificate, so the swallowed-error map branch is excluded. Successful parent completion and native entry guards remain explicit.

`native_create2_world_agreement` now relates a real successful native CREATE2 parent step to an actual `CreationStorage.commit` result for a vacant target. It derives child completion, entry account agreement after native nonce insertion, target warming and all raw world fields; original transaction storage and physical memory are retained. Native entry guards, adequate fuel, prior raw agreement and successful parent completion remain explicit. It does not yet certify parent termination, collisions, exact stack/gas/result correspondence to the full canonical caller, source channels or whole imported functions.

Actual native Lambda return gas is bounded by its input for every target state and budget; the exact CREATE2 child return is bounded by the native forwarded budget. These facts prove entered parent CREATE2 completion under its native guards and the explicit charged-parent-gas bound `< 2^255`, which prevents UInt256 addition wrapping. Child completion and gas bounds are derived; exact parent stack/status/gas and canonical caller correspondence remain separate.

`native_create2_world_completed` combines derived native parent termination with the actual canonical `CreationStorage.commit` and full raw world agreement, without a supplied parent-completion premise. Its scope remains zero value, vacant target, supported initcode, sufficient fuel, native entry guards, prior raw agreement and charged gas below `2^255`. Exact caller stack/gas/status correspondence, collision-world transport, source typed channels and whole-function authenticity remain unfinished.

`native_create2_complete_observations` additionally derives the exact native caller stack/status guard, remaining gas, return bytes, PC, execution length and active memory words alongside actual completion and raw world commit. This does not yet identify those observations with the full canonical `Create2Operation.run` result, prove collision-world transport, or establish source typed-channel and whole-function authenticity.

`native_create2_collision_world` derives actual native parent completion and raw world agreement for nonce/code collisions after the creator nonce bump. It retains persistent/transient storage, original transaction storage and physical memory, and warms the target. Native entry guards remain explicit; collision execution requires no supported-initcode premise or extra charged-gas bound because child return gas is zero. Canonical collision reservation/commit identification and full caller/source authenticity remain separate obligations.

`native_create2_collision_committed` identifies actual native collision completion with an actual canonical failed `CreationStorage.commit`. Native nonce/code occupancy implies canonical collision reservation, including creator/target aliasing; canonical callee failure consumes all child gas and returns no bytes. Full canonical caller preparation/gas/status correspondence and source/whole-function authenticity remain unproved.

`NativeCreate2RejectedEntry` proves the exact raw native parent state for creator nonce refusal and failed depth/size entry guards, with zero endowment and explicit charged gas below `2^255`. No child executes, accounts and warm state remain unchanged, and forwarded gas is fully returned. Native nonce `>=` refusal is retained; equivalence to the canonical uint64 domain and outer static/size exceptional checks remains a separate obligation.

`NativeCreate2CallerGas` identifies actual completed native parent gas with EIP-150 retained gas plus actual child return, and hence canonical `completeGas` for that split. The return bound and child completion can be derived from actual supported-initcode execution. This does not yet establish that canonical `prepare` charges precisely the native opcode/memory costs, or authenticate a whole function.

`NativeCreate2EntryCost` proves canonical physical caller-memory word count, actual native base/hash/initcode cost, and memory-expansion cost equal the canonical entry charge. `native_create2_prepare_forwarded` derives canonical preparation from those actual costs under explicit gas/static/size/depth guards and memory-counter no-wrap. Native modular debit normalization, physical slice/address agreement and full caller/source execution correspondence remain separate obligations.

`NativeCreate2GasDebit` proves the actual sequential native memory/instruction word debits equal natural gas subtraction under their successful funding guard. Canonical preparation uses this exact debited budget; the input uint64 gas bound derives the earlier `< 2^255` parent bound, and `native_create2_funded_completed` derives actual parent completion after native memory metering. Physical slice/address and complete source/caller authenticity remain separate obligations.

`NativeCreate2MemorySlice` proves actual native padded windows equal full canonical physical initcode slices, before and after canonical caller-memory expansion. The constructor cap derives host padding-count no-wrap on both supported platform widths. The native allocation-within-active-memory invariant is explicit; its preservation through whole caller execution, exact native/canonical address hashing and full function authenticity remain required.

`NativeCreate2AddressChecks` independently compares the opaque native Keccak FFI against the pure Lean engine on 54 CREATE2 cases: creator/salt encodings, inner hash, all 85 outer-preimage bytes, outer hash, low-160-bit result and a raw-initcode substitution sentinel. This is sampled runtime evidence, not a universal theorem equating opaque FFI with pure Keccak. The full native/canonical address proof must expose that primitive boundary explicitly; no project axiom or unconditional equivalence has been introduced.

`NativeCreate2AddressEncoding` universally proves native/canonical fixed-width bytes, the 20-byte creator, 32-byte salt/digest words, marker and complete 85-byte preimage. These encoding proofs do not assume hash-engine equality. Relating the actual inner digest, opaque native Keccak and low-160-bit truncation to the complete canonical address remains an explicit obligation.

`NativeCreate2DigestBytes` proves the actual native packed-byte list observation, fixed-width decode/encode roundtrip and exact 32-byte digest roundtrip including leading zeros. It composes the actual digest bytes into the canonical preimage using the native decoded value. Equality with the canonical big-endian decoder, final low-160-bit truncation, and the opaque Keccak primitive boundary remain separate obligations.

`NativeCreate2LowBits` proves native low-byte extraction equals modular reduction and, for every 32-byte digest, extraction `[12,32)` equals reduction modulo `2^160`. The actual CREATE2 target composition retains the opaque outer hash output-size premise explicitly. No universal hash size/equality axiom is introduced; canonical decoder agreement and the primitive hash boundary remain required.

`NativeCreate2BigEndian` proves the actual `ByteArray.foldl` loop traverses the packed bytes and universally equates the canonical big-endian decoder with native `fromByteArrayBigEndian`. This removes the decoder bridge obligation without assuming hash agreement. The opaque Keccak primitive boundary and full caller/source authenticity remain explicit unfinished obligations.

`NativeCreate2AddressAgreement` composes both actual CREATE2 hashes, all preimage bytes and low-160 truncation into complete native/canonical address equality. It also connects the actual native padded caller-memory slice to canonical physical-memory address calculation. Two pointwise primitive Keccak agreement hypotheses are explicit; the physical bridge retains the allocation invariant. These are conditional kernel proofs, not universal opaque-FFI equivalence or whole-function authenticity.

`NativeCallerAllocation` proves a universal upper bound for actual native `ByteArray.write` allocation, including zero-length copies and host padding-count truncation. It preserves allocated-bytes-within-active-words through actual MSTORE, MSTORE8, MLOAD, calldata/code/return-data copies and overlapping MCOPY, with explicit active-word no-wrap and store-padding bounds. The MSTORE rule also composes with the actual opcode step. Deriving bounds from checked gas and preserving the invariant across every caller-prefix step remain required; this module alone does not authenticate whole caller execution.

`NativeCallerAllocationBounds` derives active-word no-wrap universally from actual UInt256 operands, including MCOPY source/destination maxima. Together with the real write-size bound it proves allocation preservation for MSTORE/MSTORE8, MLOAD and all caller copy primitives without independent host-padding or word-no-wrap hypotheses. Opcode dispatch and whole-prefix composition remain separate obligations; no gas guard is weakened.

`NativeCallerAllocationSteps` proves allocation preservation for every opcode in the existing local caller whitelist, the actual checked step and the full executed `CreationCaller.run` prefix reaching CREATE2. The complete physical initcode slice therefore agrees with native padded reads from an allocated initial caller, with no independently supplied boundary allocation premise. This does not establish whole source-function authenticity or equate opaque Keccak primitives.

`NativeCreate2OperationRun` proves complete Midnight-initcode decoding, exact canonical forwarded-operation composition, reservation from the actual bumped native account map and canonical `runEntered` status/gas/outcome for the same actual child invocation. The native child completion and reservation are derived, not supplied as independent oracle results. Composition with the complete actual native caller, prepared address and storage commit remains unfinished; this does not admit CREATE2 at the importer boundary.

`NativeCreate2PreparedAddress` identifies the native target with the canonical prepared-world target, retaining both pointwise opaque Keccak agreements, and derives the actual complete slice, caller owner, raw account/storage agreement and canonical nonce guard. `native_create2_child_world` now retains its already-proved reservation. The new entered-world composition uses deterministic equality of the actual child invocation and that reservation to combine canonical `runEntered`, existing storage commit and complete raw parent-world agreement for the same result. Complete caller-result and whole source-function authenticity remain unfinished.

`NativeCreate2CallerPreparation` preserves raw world agreement and caller allocation through actual memory gas metering, derives canonical preparation without an independent active-word no-wrap premise, proves exact padded-read size, and derives zero-value entry and completed native parent execution from initial guards. Full canonical caller-result correspondence and whole source-function authenticity remain unfinished; the pointwise opaque Keccak boundary remains explicit.

`NativeCreate2CanonicalEntry` derives canonical entry on the complete prepared physical initcode and actual two-hash target from native nonce/vacancy guards. `NativeCreate2CallerOperation.caller_operation_completed` derives both actual native completion and the full canonical `Create2Operation.run` result with raw final world agreement and exact caller gas. Its guard record contains initial machine facts and the two explicit pointwise Keccak agreements, with no selected child/outcome/final-state certificates. Stack/result-value and remaining caller observations, typed channels and whole Solidity function authenticity still require composition; CREATE2 importer admission remains closed.

`NativeCreate2CallerValue` derives the actual child address and empty return bytes, eliminates all false entry branches of the native status guard and relates the resulting stack word to the canonical outcome value. The strengthened `caller_operation_completed` additionally carries `CallerResultObservations` for that same canonical result: exact stack, empty returndata, PC/execution-length increment, active-word update, original account map, physical byte buffer and environment. No child outcome is supplied independently. Canonical final physical-memory extent/byte agreement, typed storage/event/context framing and whole-function authenticity remain separate obligations.

`NativeCreate2CallerMemory` proves exact canonical prepared extent against the actual native word update, allocation preservation at continuation, every physical byte observation including zero tails, and unchanged physical memory through the real storage commit. The strengthened `caller_operation_completed` now additionally derives complete final `CallerPhysicalMemoryAgreement` for the same canonical result and native continuation. These conditional opcode-boundary proofs retain both pointwise Keccak agreements; typed channels/events/original/refund/context framing and whole-function source authenticity remain unfinished.

`NativeCreate2CallerFrames` retains the complete canonical context/event/call/metadata frame, every storage channel outside the actual new target persistent namespace, and native logs/refund/storage-access/destruction bookkeeping (accessed accounts are the sole substate change). Existing tracked typed-to-flat coherence transports to actual final native slots without a hash-injectivity axiom. The strengthened `caller_operation_completed` returns these frames for the same full canonical/native operation result alongside its prior stack/gas/world/physical-memory assertions. Whole-function source authenticity and gas/static/depth/nonce/collision path composition remain obligations before importer admission.

`NativeCreate2CallerChecks` derives both native exceptional-check gas gates from the combined initial budget and proves the actual upstream `Z` checks for a funded, mutable CREATE2 with valid stack and size. `caller_checked_operation_completed` connects actual `EVM.X` to the same native continuation and canonical operation, retaining all prior value, gas, world, physical-memory and frame assertions. Decoded CREATE2 and the initial stack limit are explicit hypotheses. The two pointwise Keccak agreements remain explicit. Rejected/static/gas/depth/nonce/collision branches and whole source-function authenticity remain required before importer admission.

`NativeCreate2CallerDepth.caller_depth_operation_completed` derives the complete checked-native/canonical depth-refusal continuation: zero value, exact refunded gas, raw world agreement, every caller observation, full physical-memory agreement, and storage/event/context frames. Native accounts and the entire substate, including accessed accounts, remain unchanged. Canonical warm accounts remain unchanged. Constructor bytes and Keccak agreements are unnecessary because this path refuses entry before computing an address. Native nonce legality remains an explicit initial premise; nonce-refusal, exceptional and collision paths and whole-function source authenticity remain separate obligations before importer admission.

`NativeCreate2CallerExceptional.caller_exceptional_operation_completed` connects actual native `Z` and `EVM.X` exceptional rejection to the full canonical exceptional result for unfunded gas, static mode, or oversized initcode. The exact native reason retains gas-before-static-before-size ordering; canonical gas becomes zero. The opcode-entry memory, raw account/storage agreement, complete other-field world frame, storage words and warm accounts are preserved. No constructor or hash outcome is supplied. This is opcode-entry correspondence, not yet outer transaction rollback or whole source-function authenticity. Native nonce/collision and whole-function composition remain required before importer admission.

`NativeCreate2CallerNonce.caller_nonce_operation_completed` proves complete checked-native/canonical nonce refusal at the exact uint64 maximum. Both executions return zero, refund all forwarded child gas, and preserve accounts, the entire substate, warm accounts, storage, events and every caller/physical-memory observation. The actual initial account agreement derives the canonical nonce; neither constructor bytes nor hash results are supplied. Nonces above uint64 remain outside the canonical account projection and must fail closed. Collision and whole source-function authenticity remain obligations before importer admission.

`NativeCreate2CallerCollision.caller_collision_operation_completed` derives the complete checked-native/canonical collision result from initial native guards, actual bumped occupancy and two explicit pointwise Keccak agreements. The same computed target and child determine zero return, retained caller gas, creator nonce insertion, target warming, final raw world agreement, all caller and physical-memory observations, every storage word, and the complete remaining world/substate frame. Constructor bytes are not decoded on collision. Whole source-function authenticity and execution-context integration remain required before importer admission.

`NativePairedCallerAllocation` proves actual checked persistent/transient writes and every admitted paired-prefix step preserve physical allocation. Its bounded prefix theorem derives allocation and raw world agreement at the actual CREATE2 boundary. `run_ready_creation` then derives the complete checked-native/canonical funded result from that computed boundary world, retaining every prior assertion; it does not substitute the stale entry world. A relation between the paired prefix and whole `EVM.X`, source hashed-channel authenticity and whole-function context remain required before importer admission.

`NativePairedCallerFuel` proves positive-fuel independence for every paired-prefix primitive, including actual persistent/transient writes. Successful checked steps therefore retain their exact native result at any positive interpreter fuel. It also proves the parser is total over all bytes (unknown bytes become INVALID) and both jump-destination scanners agree for word-addressable code, including PUSH-data skipping. These are universal bounded-code theorems, not sampled scanner agreement. `NativePairedCallerChecks` derives all original checked-step guards and proves actual native `Z` success with the exact memory/instruction gas debit. It translates JUMP/JUMPI optional stack reads using derived operand presence and the proved scanner equality, and proves the full paired whitelist has the same native static predicate and never halts or creates. Every successful paired step therefore continues the actual `EVM.X` iterator at any positive primitive fuel. These are success correspondences; they do not assert identical exceptional-check ordering. `NativePairedCallerExecution` now derives a positive remaining-fuel count from every successful paired run reaching CREATE2 and proves actual whole-prefix `EVM.X` continuation for every extra fuel amount. The executing bytecode/environment and native jump scanner are preserved, including across actual persistent/transient writes. `NativePairedCallerBoundary` derives the consumed prefix step count and the actual CREATE2 decode from readiness, then composes the full native prefix with funded CREATE2, preserving the complete canonical result, gas, raw world, physical memory and storage/substate frames from the computed boundary world. `NativePairedCallerRefusals` composes the same actual prefix with depth refusal, exact-max nonce refusal, collision and exceptional CREATE2 branches, retaining all their canonical/native observations and frames. Exceptional native reason ordering is preserved without claiming surrounding transaction rollback. Source/bytecode identity, typed hashed-channel authenticity and whole-function context/observations remain required before whole-function/importer admission.

`NativeHashedStorageAgreement` connects aligned persistent/transient mapping-chain shadow writes to successful actual checked SSTORE/TSTORE at the compiler-computed slot. It reuses finite tracked layout certificates and preserves every raw native agreement field while proving each tracked typed word equals actual native storage. No universal hash injectivity is assumed. Authentic source-write/prefix composition, source/bytecode identity and whole-function observations remain separate admission obligations.

`NativeSourceMappingWrites` proves the actual Source mapping-chain helpers with one base slot agree with checked native SSTORE/TSTORE at their exact folded Keccak location, including the persistent/transient field dispatch. These helpers write physical slots; no symbolic shadow update is silently inserted. Full source statement/operand sequencing and source-bytecode identity remain required.

The typed Source executor now handles `setMappingChain` by evaluating keys in order, then the value in the resulting key state, and only then consuming the resolved write. Missing fields remain interpretation errors, and operand refusals propagate unchanged. This does not open importer admission or establish whole-function native correspondence.

`NativeSourceMappingExecution` composes actual typed mapping-chain operand evaluation with the actual checked SSTORE/TSTORE result and native `EVM.X` continuation. The raw world relation is required at the operand poststate; native stack operands and decode are still explicit premises. Their derivation from source/bytecode identity and whole-function correspondence remain open.

`NativeSourceStorageBytecode` derives SSTORE/TSTORE and PUSH32 decoding from actual bytes at the native PC. Two successful byte-authenticated checked PUSH32 steps derive both stack operands, their exact PCs (including UInt256 wraparound), the unchanged account world and actual EVM.X continuation. The PUSH32 values are read from the real following code bytes, not supplied as stack premises. Checked-step success and the two opcode bytes remain hypotheses; this is not source-bytecode identity or a whole-function certificate. Authenticating the mapping hash computation and remaining source context is still required before importer admission.

`NativeMappingKeccak` proves that the actual helper order MSTORE(0,key), MSTORE(32,base) materializes exactly key followed by base in 64 bytes, even with initially empty memory. Real checked stores and KECCAK256 then derive the model mapping-slot word under an explicit FFI/pure hash equality at this one preimage. Its native Z/gas and byte-authenticated EVM.X continuation are proved separately. This does not change the paired caller opcode whitelist or importer admission. Actual source operand/bytecode identity and whole-function observations remain required; no universal native/pure hash equality is asserted.

`NativeMappingStorageExecution` derives the intermediate stacks and whole native account-world frame of a MSTORE/MSTORE/KECCAK256/storage-write fragment from one initial stack and actual checked execution. It composes the computed hash into the actual source mapping-chain statement, including literal normalization and persistent/transient field dispatch, and separately composes the same four byte-authenticated instructions in EVM.X. Initial raw world Agreement and account presence suffice; a final-stack or hash-poststate Agreement oracle is not required. The hash uses an explicit pointwise FFI/pure equality. This is a fragment theorem, not identity with an entire generated helper bytecode or whole-function certificate; the paired caller whitelist and importer admission remain unchanged.


`NativeCapturedMappingHelper` authenticates and proves the actual optimized solc 0.8.34/Osaka
output of an isolated wrapper around the real `CodegenCommon.mappingSlotFuncAt 0` helper.
`scripts/check_native_mapping_helper_capture.py --check` exports the generator through Lean,
checks the pinned compiler hash, regenerates both compiler variants and their full requests/results,
and rejects differences in the proof's bytecode and decoder prefix. Artifacts and source/tool
identities are preserved under `artifacts/native-mapping-helper`.

For the optimized twenty-byte wrapper, the Lean proof derives all sixteen instruction transitions
and actual checked guards. Code identity, PC0, an empty stack, zero active words and at least85
gas suffice for real native execution to halt; calldata and physical memory are arbitrary.
It proves exactly85 gas spent, the full account-world frame, original stack, and model mapping-slot
return bytes under explicit pointwise `ffi.KEC`/pure Keccak equality at the actual calldata preimage.
No successful-step, intermediate-state or final-state oracle is assumed. The native smoke fixture
checks64 executions at84/85/86/100000 gas and1056 successful intermediate boundaries, including
expected out-of-gas at84. These samples do not establish universal hash agreement.

This is an isolated generated helper certificate. The compiler capture remains an executable
provenance check, not a theorem about solc itself. It does not certify a complete Midnight function,
the source caller's ABI/context or its composition with storage and creation. CREATE2 admission
and the paired-caller KECCAK whitelist remain unchanged; whole-function exact observations and
the original differential/publication gates are still required.


`NativeHashedWorldCaller` extends the checked storage-aware prefix with actual KECCAK256, preserving canonical/native world agreement and allocated memory. The real decoded prefix supplies its CREATE2 boundary, step count and native continuation; checked creation is composed from that same computed world under explicit `CallerOperationGuards`. Nineteen public laws are audited with only standard Lean axioms. Sixteen persistent/transient hash/storage/creation cases also agree with pinned Foundry, including exact gas at the boundary, after creation and at return. Runtime mutants detect erased hash, stale world and skipped hash execution. These are component results for explicit bytecode, not imported whole-function equivalence. The old paired opcode whitelist and importer CREATE2 admission remain unchanged; source ABI/context and complete observations still require whole-function linkage.


`NativeHashedDenote.atBoundary` projects the computed native-prefix world, physical memory and ephemeral opcode context into a Denote boundary state. Its two laws compose actual prefix/native CREATE2 with `Denote.execCreation`, preserving the same result, world and gas under the explicit creation guards. This projection does not prove correspondence with the source statements preceding that boundary. Runtime checks retain unrelated bindings and external-call inputs, and reject absent context or a stale pre-prefix world. CREATE2 importer admission remains closed pending the source-prefix, ABI and whole-function observations.

The captured Midnight caller instrument now lives in the repository. Run
`python3 scripts/check_native_midnight_source_capture.py --check` to regenerate
the pinned solc 0.8.34/via-IR/Osaka output from checked-in IdLib and IMidnight
sources at Midnight `96d31343`. Its 977-byte runtime and six dynamic Market
inputs are exercised by `NativeMidnightSourceChecks`, including the real ABI
decoder, mapping write, initcode, native CREATE2 and full native continuation.
The global mutation command retains the source-caller success line and checks
three executable captured-code/ABI mutations with independent replays.

`python3 scripts/solidity_differential/check_native_midnight_source.py --output <new-directory> --foundry <pinned-foundry-directory>`
compares fresh Foundry transactions with those native/canonical/Denote-boundary
observations, including return bytes, touched storage, events, creation gas,
deployed runtime and nonces. The Linux Foundry 1.5.0 binaries and solc are hash
pinned. This is calibration of the actual source bytecode, not an imported
whole-function A/B/C campaign or source-prefix equivalence proof. No supported
Solidity construct is added; CREATE2 importer admission remains closed.

The same portable capture also generates 24 malformed Market ABI controls in
bounded 64-byte Lean constants (truncated selector/tail, dirty address, oversized
root offset). `NativeMidnightInvalidChecks` executes the actual solc runtime and
requires empty revert bytes. `NativeMidnightCollisionChecks` covers all six
canonical inputs with target nonce or code occupancy: zero creation result,
exact gas, retained operation-boundary mapping write, creator nonce bump,
preserved target account, then the source's custom-error continuation.
Both execute from the separate bounded global native-refusal check. Refusal mutations remove a
native/canonical collision or replace a malformed ABI input with a valid one;
detection must be an actual assertion failure with an identical replay.

Run `scripts/solidity_differential/check_native_midnight_collision.py` or
`check_native_midnight_invalid.py` with the same `--output`/`--foundry` arguments
as the success instrument for the fresh Foundry reference. Collision transactions
must revert with identical bytes/gas and roll back the mapping/creator nonce
while preserving the occupied target. Malformed inputs must revert empty before
any storage write, creation or event. These bytecode controls do not certify
importer diagnostics or native transaction rollback-world semantics: native
`EVM.X` exposes revert gas/bytes but not the reverted world.

`scripts/check_native_midnight_rollback_capture.py --check` also authenticates a
separate actual caller that successfully deploys through pinned IdLib, emits
`Created(address)` and reverts with `AfterDeploy(address)`. The 1026-byte runtime
and six dynamic Market inputs are exercised by `NativeMidnightRollbackChecks`;
a separate bounded global runner retains the exact native revert checks.
`check_native_midnight_rollback.py --output <new-directory> --foundry <directory>`
compares the real EVM trace and committed rollback, including child success,
nonzero creation result, exact transient event, revert bytes/gas and undone
mapping/code/nonces/events. The global mutation driver detects corrupted storage,
initcode and custom-revert bytes through actual assertions and independent
replays. This remains a bytecode calibration rather than importer admission or
a universal native transaction-world rollback proof.

### Explicit initial account inputs in stateful validation

The stateful CLI accepts `--initial-accounts FILE`, a JSON array of external
accounts with exactly `address`, `code`, `nonce` and `balance`. Addresses use
canonical 20-byte hex, code uses full hex bytes (including leading zeroes), and
nonce/balance are JSON integers fitting uint64/uint256. Duplicate accounts and
addresses reserved for deployments or transaction senders are rejected before
installation. Anvil installation reads every field back. The Lean adapter
receives the full byte array and installs coherent code-size/account projections;
unrelated storage, memory and events are preserved.

Each real EVM route archives its own deployed caller account. The CLI supplies
the source deployment's exact runtime, nonce and balance to Denote, read at the
successful deployment receipt block with block-hash verification. Source and
Verity runtimes remain distinct artifacts. Caller balance and code-size views
are installed consistently; omitted account inputs retain the legacy empty
projection. This input mechanism does not add Solidity external-code queries,
CREATE2, an opcode gas context, or self-code equivalence. The six-case prefix
campaigns validate initial inputs without claiming execution of these constructs.

`check_account_inputs` checks canonical inputs, historical caller capture and
real-node semantic mutations; `check_account_input_mutations` requires nine
cleanly compiled Lean mutants to fail unchanged runtime assertions and replay.


`CreationMemoryWhole.operation_equivalence` (in namespace
`Compiler.Proofs.IRGeneration.CreationMemoryOperation`) proves complete
`Create2Operation.run` result equality after erasing only caller memory. It assumes
equal complete nonmemory worlds, exact physical initcode slices, active memory
extents and the same actual opcode context and warm accounts. It covers all
preparation results, all creator nonces and exact unsupported errors; forwarded
gas and memory are derived from preparation. Neither execution substitutes the
other's memory. These conditional operation laws do not establish the premises
for arbitrary imported source prefixes or equate source and compiled caller
code/gas. `CachedCreationCaller` proves whole checked-step, advancement and runner
equality with `NativeHashedWorldCaller`; cached jump tables are reused only after
exact code equality, and recomputed on changes. All native guards and outcomes
remain. These are proof and instrumentation additions; CREATE2 importer admission
remains closed pending source-prefix and public execution-context integration.

`CreationMemoryLayout.covered_layout_equivalence` (in namespace
`Compiler.Proofs.IRGeneration.CreationLayoutOperation`) additionally permits
different initcode pointers and memory extents. If both exact byte buffers are
already allocated, their entry costs and forwarded gas agree under the common
actual context. Full nonmemory world equality and the legal creator nonce remain
explicit prerequisites. This is a conditional operation proof, not a proof that
arbitrary source and compiled prefixes establish those prerequisites.

`CreationStatementRelation` lifts the complete and covered-layout operation
relations through the actual `Denote.execStmt .create2` dispatcher. Its observation
erases only caller memory: all other state, bindings, context, outcome constructors
and revert bytes remain. The same common actual context and independent-prefix
premises are required. This bridge neither attaches a guessed context nor admits
CREATE2 into the Solidity importer.

`ImportedPrefixFrames` proves that its recursive memory/local/control whitelist
preserves the entire nonmemory world, including all storage and account functions.
The real imported `ImportedCreationPrefixFrames` fixture has a kernel-checked
certificate: its 91 top-level prefix statements split into 38 certified statements,
one mapping write and 52 certified statements. `actual_prefix_isolate` derives
the actual intermediate write execution from any successful prefix run, with
complete nonmemory frames on either side. This does not yet relate the mapping
write to the executed native prefix or prove its initcode bytes, allocation or
context for arbitrary inputs. CREATE2 source admission remains closed.

`ImportedMappingEffect` proves the complete persistent singleton mapping-member
write equation and its nonmemory frame. The imported-prefix fixture additionally
proves that the analyzed instruction is the actual node at index 38 and composes
its complete state equation with both certified memory/control segments.
`actual_prefix_effect` therefore describes the whole nonmemory world for every
successful prefix run as the initial world with one actual mapping write. Its
key/value are the locals at that step; relating those locals to ABI inputs,
then linking native execution, initcode bytes and actual context, remains open.

`ImportedAbiOperands` proves the exact symbolic execution and binding values of
the two calldata loads at offsets 36 and 68. The actual imported-prefix fixture
certifies that these are its final pre-write instructions, preserves calldata
through the preceding ABI setup, and proves `actual_prefix_abi_effect`: the entire
nonmemory result of any successful prefix is the original world with one mapping
write whose key/value are the original ABI words 1/2, normalized as uint256.
No arbitrary local-binding hypotheses remain. Native slot/hash/write linkage,
initcode memory and real opcode-context composition still require proof.

`NativeSourceAbiWrite` certifies the 13 decoded instructions at PCs 404–420
of the pinned 977-byte Solidity source caller runtime. For arbitrary calldata,
initial stack and memory, every successful checked run of that fragment derives
the key from calldata offset 36, the value from offset 68, and the exact Keccak
preimage (key followed by zero base). Under explicit pointwise FFI/pure Keccak
agreement and actual account presence, the real SSTORE preserves raw native/world
agreement and the paired instrument performs the complete canonical-world write.
No intermediate stack, chosen postworld or successful final store is supplied.
The fixed decode certificate uses kernel `decide` with local recursion depth 8192;
no native execution decision or whole-prefix interpreter reduction is used.
Reaching PC 404 from arbitrary source entry, preserving the original transaction
calldata through that entry prefix, relating byte calldata to Denote ABI words,
and composing the remaining initcode/allocation/gas/context proofs are still open.
This fragment certificate does not open CREATE2 source admission.

`NativeSourceEntryWrite` executes the original local entry prefix to computed
PC404, then the actual 13-instruction mapping fragment. Successful runs preserve
the entire pre-write native State (including original calldata/accounts),
allocation bounds, and the actual EVM iterator with a derived step count;
unsupported instructions, native exceptions and exhausted interpreter fuel are
explicit errors. The successful-run premise does not prove total success or
that every arbitrary full source run factors through this instrument.
`NativeSourceAbiInputs` reuses the existing native state bridge to prove that
byte calldata encodes the original ABI words at offsets36/68 for arbitrary
selector and arguments. `ImportedCreationPrefixRelation.entry_imported_world`
composes both independent executions and proves equality of their complete
nonmemory write effects, with explicit pure mapping-oracle and pointwise
FFI/pure Keccak premises. No native boundary world is installed into Denote.
The remaining native suffix to CREATE2, initcode/layout and actual metered
context composition are still open; source CREATE2 admission remains closed.

`NativePrefixComposition` proves equality of full continuation results when
composing the executed entry and paired fragment with the existing
`NativeHashedWorldCaller.run`; errors and exceptional outcomes of the continuation
are preserved. Its staged entry/13-step fragment/local suffix executor supplies a
real original ready run with a derived fuel count. `NativePrefixWorld` certifies
all twelve actual pre-SSTORE PCs and proves the complete single-write world effect
through the local suffix to CREATE2. The actual imported fixture theorem
`ImportedCreationBoundaryRelation.boundary_world` now relates the independently
executed imported prefix to that existing native runner's actual boundary with
entire nonmemory-world equality. Original byte-ABI identity, pure mapping-oracle
identity and pointwise FFI/pure Keccak agreement remain explicit premises, as do
both successful executions. Each side retains its own physical memory.
This proves forward composition for every successful staged execution; it does
not prove total success, reverse factorization of arbitrary original runs,
arbitrary initcode slice/layout equivalence or metered context integration into
the public Denote route. CREATE2 source importer admission remains closed.


`CreationRelocatedCopies` derives exact initcode-slice equality from actual
physical byte copies at different destination pointers, including arbitrary
header/payload lengths and zero-length copies. Its packing theorem preserves
the header across the appended payload, and its trailing-word theorem proves
that the encoder's subsequent word store beyond the slice cannot alter code.
These kernel laws do not assume equal destination memories. They still require
corresponding input bytes and must be linked to both actual prefix executions;
they do not establish arbitrary Market encoding or metered context equality.
No new importer admission or trust assumption is introduced.


`ImportedCreationCopyBytes` reuses the existing actual `copyBytes` interpreter
proof to derive physical snapshot-copy equality at every address and exact
CREATE2 slice equality, retaining all nonmemory world fields. The portable
`ImportedCreationCopySlices` fixture kernel-identifies both actual packing loops
at indices 85/87 and specializes that result to them. Bounds, freshness, source
and destination alignment, nonoverlap, original input bindings and initial zero
bytes remain explicit preconditions; they are not assumed post-copy equality.
Discharging those conditions from the complete prefix, relating its arbitrary
Market ABI bytes to native execution, and metered context integration remain
open. These results do not admit source CREATE2 or move the trust boundary.


`ImportedCreationPacking` composes two executed copy invariants into the exact
combined initcode slice from the original header/payload snapshots. It derives
payload-zero and source-preservation facts across the header copy.
`ImportedCreationCopyBindings` separately proves that successful actual
copy-body/loop/statement executions preserve every protected local, including
the zero-iteration index binding. The actual `ImportedCreationPackingFrames`
fixture identifies the intervening index-86 assignment and derives payload
descriptors/count by executing it after the real header loop. These results
retain original input obligations: they do not yet derive allocation geometry,
zero initialization, arbitrary ABI contents or native metered context from the
complete prefix, and source CREATE2 admission remains closed.


`ImportedLocalFrames` certifies an explicit recursive memory/local/control
whitelist preserving a protected local, including loop-index rebinding. Unknown
statements are rejected by that certificate. `ImportedCreationAllocator`
identifies actual nodes 78–84 and executes them to derive cleared physical bytes,
coherence and retained copy descriptors. `ImportedCreationAllocatedPacking`
then executes the actual ten-statement allocator/header/increment/payload segment
and derives its whole initcode slice from the allocated state's source snapshots.
Zero initialization and coherence are conclusions, and word bounds follow from
the allocation ceiling. Initial descriptor bindings, alignment, source/output
separation and allocation ceiling still require the earlier actual ABI/encoding
execution. Snapshot identity across the allocator, native slice/layout agreement
and actual metered context are not yet established; source CREATE2 stays closed.


`ImportedCreationOriginalSnapshots` derives the actual allocator's entire
physical world, frames its free-pointer and clearing writes away from the two
source intervals, and strengthens the executed packing segment to ORIGINAL
segment-entry snapshots. Sources must be at/above byte 96 and finish before
the destination; these remain earlier-encoding obligations.
`ImportedCreationHeaderAllocation` kernel-identifies actual nodes 71–76, executes
that header allocator/store with exact full state, derives the eleven literal
IdLib header bytes and preserves the preceding payload. This does not yet
compose the intervening total-size binding or prove arbitrary Market ABI
contents, native memory-copy agreement or metered context. CREATE2 stays closed.


`ImportedCreationHeaderPreparation` executes actual nodes 71–77, including
the total-size let. It derives the updated free pointer, actual header pointer,
retained payload/count, total `11 + size`, original payload byte preservation
and the eleven actual literal header bytes. The word at byte 64 is framed
against the whole header store window, rather than just unequal addresses.
Initial payload descriptors, separation, alignment/allocation conditions and
arbitrary ABI contents still require the preceding encoder. Composition into
the subsequent packing segment and native metered context remains unfinished;
no additional Solidity construct is admitted.


`CreationPackedBytes` proves exact physical-slice splitting and concatenation
for arbitrary header/payload copies, including empty payloads. The actual
`ImportedCreationPackedCode.execute` theorem now executes nodes 71–87 and proves
that the final complete initcode slice is the literal eleven-byte IdLib prefix
concatenated with the ORIGINAL segment-entry payload slice. Header/pointer/total
descriptors, intermediate worlds, coherent zero buffers and output bytes are
derived by execution. Initial payload pointer/count, alignment/separation and
allocation ceiling still require the earlier ABI encoder; arbitrary Market ABI,
native prefix/layout and metered context are not proved by this segment.
Source CREATE2 importer admission remains closed.


`ImportedCreationLength.execute` now executes actual nodes 70–87 and derives
the payload length from the actual EVM word subtraction of the source pointer
from the free pointer. The resulting exact literal-prefix/original-payload
bytes no longer require a supplied size local. Pointer ordering, alignment
and the allocation ceiling remain explicit prior-encoder obligations.
`ImportedCreationArrayAllocation` identifies actual nodes 54–58, proves their
`32 + 128 * count` arithmetic without modular wrap under the allocation guard,
and derives their exact whole-state reservation. It does not prove the dynamic
element loop, arbitrary ABI bytes or native/context agreement. No new Solidity
construct is admitted.


`ImportedAbiWordCopy` proves an actual coherent `mstore(mload)` is an exact
32-byte snapshot copy of the complete world, including memory expansion and
all overlapping word views. `ImportedAbiWords` derives original-source bytes
and the full outside-destination byte frame for sequential copies under explicit
region separation. `ImportedCreationArrayElement` kernel-identifies actual
loop 61, executes its pointer-array load and all four stores, and derives the
complete 128-byte original struct snapshot plus the outside byte frame.
Pointer bindings, no-wrap bounds, coherence and region separation remain
explicit obligations for the preceding decoder/allocator and the whole-array
invariant. This proves one actual element, not the arbitrary-count loop or
complete ABI/native equivalence. Source CREATE2 admission remains closed.


`ImportedAbiArray` proves arbitrary-count element snapshots, the complete
outside-destination byte frame, coherence and exact pointer-word preservation.
`ImportedCreationArrayLoop.execute` now executes actual node 61 for any count
allowed by the allocation ceiling, including zero. It derives the entire world
and actual binding evolution. Every output element is the ORIGINAL loop-entry
struct selected by its ORIGINAL pointer-array word; shared source pointers are
allowed. Array pointers and all structs must precede the output reservation,
and those geometry facts remain obligations for the earlier decoder/allocator.
The complete ABI head/tail initialization, original transaction ABI relation and
native metered-context composition remain open. CREATE2 admission stays closed.


`ImportedCreationHeadAllocation` executes actual nodes 39–44: the 288-byte
static head reservation and root tuple offset32. It derives the complete state,
updated free pointer, root word and preservation of original inputs at96 or
above before the new head. `ImportedCreationArrayHeader` executes nodes59–61:
the real dynamic offset is derived as256, the length is stored from the count
binding, then the entire arbitrary-count loop executes. Its output snapshots
refer to ORIGINAL pre-metadata structs and pointers; both metadata words are
retained after the loop. Input geometry and the preceding head-field copies,
pointer/count extraction and allocation composition remain open obligations,
as do complete original ABI/native equivalence. CREATE2 admission stays closed.


`ImportedAbiWordBinding.execute` proves the actual `let(mload)`/`mstore(local)`
pair is a complete physical snapshot-copy state, with its generated binding.
`ImportedCreationHeadFields` kernel-identifies and executes actual nodes45–50
and62–69 (all seven static Market field pairs). Its general sequence law derives
original source bytes when inputs precede output, preserves every byte outside
all destinations, and retains protected descriptors. Actual address expressions
and every temporary name are covered. `ImportedCreationArrayDescriptors` executes
actual nodes51–53, deriving the array pointer, count and data-base=pointer+32
from real memory reads, while retaining the entire world. These pieces are not
yet composed with head/dynamic reservation into the whole39–69 encoder or with
the original transaction decoder/native context. CREATE2 admission stays closed.


`ImportedCreationFieldFrames` protects whole field sequences' descriptors,
coherence and full word windows. `ImportedCreationPrelude.execute_full` now
executes ALL actual nodes39–69: both reservations, root word, both static-field
groups, array descriptor reads, metadata and the arbitrary-count array loop.
Pointer/count/base descriptors are derived from original encoder-entry memory,
rather than assumed at intermediate boundaries. Complete original array-element
bytes survive both allocators and all field/metadata stores. The actual final
free-pointer word equals `head + 320 + 128 * count`. Original source windows must
still lie at96orabove before the output head, and all allocation bounds remain
explicit. Complete head-byte layout observations, the original transaction
decoder geometry and native metered-context agreement remain open; this is not
yet full original-transaction ABI equivalence. CREATE2 admission stays closed.


`ImportedCreationAbiLayout` derives EVERY byte of the complete ABI payload from
original encoder-entry inputs: root32, first three fields, offset256, last four
fields, count and all pointed-to four-word array elements. It proves exact full
ByteArray equality, with no target buffer/trace supplied as a premise.
`ImportedCreationEncodedPacking.execute` executes actual nodes39–87 (49 real
instructions) and derives final initcode=`literal eleven-byte prefix ++ abiBytes
originalInputs`. The actual free pointer derives payload length and output base;
all intermediate descriptors, allocation buffers and copied bytes are derived.
Original input coherence/geometry, alignment and the full allocation ceiling
remain explicit. Deriving those from the actual preceding transaction decoder
and proving native ABI/MCOPY/metered-context agreement remain open. Source
CREATE2 admission stays closed.

`ImportedCreationDecoderAllocation` identifies and executes actual decoder nodes 5–9: the 256-byte Market reservation. Its exact state theorem derives the pointer update, coherent physical memory and the byte frame outside allocator word 64–95. This remains conditional on the entry free pointer and 64-bit allocation bound; calldata guards, field materialization, array decoding and the complete original-transaction/native relation remain open. CREATE2 admission remains closed.

The same module executes actual node0 allocator initialization (128), derives source128 and next384 for the subsequent reservation, and proves its concrete geometry. The four intervening calldata instructions are not skipped by any whole-prefix theorem: their successful execution and binding effects still require proof.

`ImportedAbiTupleHead` derives the real signed remaining-length guards from natural calldata bounds, checks the 64-bit root offset, and executes all four tuple-head instructions with the exact original-calldata pointer binding. `ImportedCreationDecoderHead` identifies and executes actual nodes0–9, composing allocator initialization, all root checks and Market reservation. Its exact whole-state result derives source128/free384, root pointer, coherence and every byte outside64–95. Explicit entry conditions are calldata size≥100 and below2^255, root offset≤2^64−1, and tuple root+256 within calldata. There is no assumed evaluated guard or intermediate postworld. Field/array decoding, mapping write, invalid-input characterization and native/public-context equivalence remain open; CREATE2 remains closed.

`ImportedCalldataWord` executes actual calldata loads/stores with complete physical poststates, canonical scalar bounds, all32 stored bytes and outside-byte frames. `ImportedCreationDecoderFields` executes actual nodes10–14 (three fields, two canonical-address guards) and composes actual nodes0–14 from original transaction calldata. It derives all96 field bytes, coherence, preserved input descriptors and free pointer384. Explicit original root bounds and canonicality of the two address words remain input conditions; invalid-input characterization, dynamic-array materialization, remaining fields/mappingwrite and native/public-context equivalence remain open. CREATE2 admission remains closed.

`ImportedAbiBounds` proves actual unsigned/signed comparisons, bounded multiplication and successful allocation guards. `ImportedCreationDecoderArrayHead` identifies and executes actual nodes15–19 (array pointer, relative-offset bound, header derivation, signed header-word range and count load), preserving the entire world and deriving all three local descriptors from original calldata. Its complete actual nodes0–19 theorem composes the original-transaction prefix, under explicit root/address/relative/header availability bounds. Named input-word and size frames avoid deep repeated physical-memory reduction; proof limits are unchanged. Array allocation/payload validation/materialization, remaining fields/mapping, invalid-input characterization and native/public-context equivalence remain open. CREATE2 admission remains closed.

`ImportedCreationDecoderArrayBounds` executes actual nodes20–25: original count bound, bounded count+1/32-byte pointer-array allocation, next-pointer guards, data pointer and full128-byte-element payload range. It executes real stores26–27 and composes actual original-transaction nodes0–27 into exact state, deriving the stored count and next free pointer384+32*(count+1), coherence and outside-byte frames. Original input availability/canonicality and numerical64-bit allocation budget remain explicit; no evaluated guard or intermediate postworld premise. The actual materialization loop28, remaining fields/mapping, invalid-input characterization and native/public-context equivalence remain open. CREATE2 admission remains closed.

`ImportedCalldataFields` executes arbitrary sequences of scalar/address calldata-to-memory field copies with original-input canonicality, exact state, coherent memory and full outside-byte/binding/input frames. `ImportedCreationDecoderElementFields` identifies the final six actual instructions of decoder loop28 and executes all four element words with the two eager canonical-address guards. All128 stored bytes are derived from original calldata words. The actual element source/allocation/pointer-store prefix and arbitrary-count loop induction still need composition; descriptor and allocation hypotheses remain explicit. CREATE2 admission remains closed.

`ImportedCreationDecoderElementPrelude` identifies and executes all14 actual instructions of one decoder-loop28 iteration: source binding, signed calldata guard, real128-byte reservation, pointer-cell write, two canonical address guards and four field copies. It derives exact whole state, actual next free pointer and retained pointer-cell bytes, with calldata/binding/size/coherence/outside-byte frames. Input descriptor, original canonicality, availability and numerical allocation/separation bounds remain explicit. Bounded intermediate word/size frames avoid deep state projection; no resource limits changed. Arbitrary-count loop induction, remaining decoder and native/public-context equivalence remain open; CREATE2 admission remains closed.

`ImportedCreationDecoderArrayLoop` executes actual decoder loop28 for arbitrary count, including zero, using induction on the real interpreter. It derives original-input canonical words, exact whole state, free pointerfree+128*count, all pointer-cell words and every byte of all four fields per struct after later iterations. It preserves input/size/protected bindings/coherence and every byte outside allocator/pointer-array/element regions. Input availability, numerical bounds and pointer-array-before-elements separation remain explicit; composition with the original transaction prefix and remaining fields/mapping/native context remains open. CREATE2 admission remains closed.

`ImportedCreationDecodedArray` executes actual original-transaction instructions0–28, composing all root/field checks, pointer-array allocation and the entire arbitrary-count struct materialization loop. Intermediate descriptors, calldata/size frames, coherence and initial free pointer are derived. It proves original-input struct bytes, each actual pointer word, retained count word, final free pointer and preservation of the earlier Market object/bindings. Explicit input validity and numerical full allocation bounds remain; remaining fields/mapping, encoder/native/public-context composition and invalid-input characterization remain open. CREATE2 admission remains closed.

`ImportedCreationDecodedMarket` executes actual remaining Market nodes29–35, including BOTH canonical-address guards at offsets192 and224, and composes the full original-transaction decoder nodes0–35. It derives the pointer member384 at memory224, remaining field bytes from original calldata, coherence, retained bindings/free pointer, and preservation of the first three fields plus the full dynamic array/count/struct region. Explicit original validity/canonicality/allocation bounds remain. Key/value bindings36–37, mapping38, encoder/native/public-context composition and invalid-input characterization remain open; CREATE2 admission remains closed.

`ImportedCreationDecodedPrefix` composes actual nodes0–38: the complete Market decoder, key/value reads from original calldata and the real imported mapping write. It derives the exact whole state and slot effect and preserves physical memory, coherence and the free pointer. Original input validity/canonicality/allocation bounds remain explicit. Encoder/native/public-context composition and invalid-input characterization remain open; CREATE2 admission remains closed.

`ImportedCreationEncoderEntry` derives source128, array384, original count, actual element pointers, alignment and all encoder input windows from the real decoder/mapping output. It executes the actual49instruction encoder/packing under an explicit original-count allocation ceiling. The ABI observation remains expressed from decoded memory; original calldata byte characterization, full-prefix composition, native/public-context and invalid-input relations remain open. CREATE2 admission stays closed.

`ImportedCreationOriginalExecution` kernel-identifies and executes the complete actual88instruction prefix from the original transaction state, composing full Market decoding, the persistent mapping write, ABI encoding and literal-prefix packing. All input validity/canonicality and original-count allocation bounds remain explicit. The byte observation is still expressed through decoded memory; original-calldata ABI characterization, native/public-context and invalid-input equivalence remain open. CREATE2 admission stays closed.

`ImportedCreationOriginalBytes` derives every byte of all seven static Market fields and every field of every dynamic array element directly from the original calldata, through the complete decoder and mapping write. It does not yet establish equality of the complete ABI ByteArray or native/public-context equivalence. CREATE2 admission remains closed.

`ImportedCreationCanonicalBytes` derives every ABI byte and the complete ABI ByteArray directly from original calldata words: root32, seven fields, dynamic offset256, original count and all dynamic structs. Only the numeric allocation ceiling is needed for memory descriptor normalization. Native/public-context and invalid-input equivalence remain open; CREATE2 admission stays closed.

`ImportedCreationCanonicalBytes.execute` composes actual88instruction execution with canonical ABI ByteArray equality: produced initcode is exactly the literal prefix plus encoding expressed solely from original calldata. Original validity/canonicality and numeric allocation guards remain explicit; native/context and invalid-input equivalence remain open, so CREATE2 admission remains closed.

`NativeSourceMcopy` proves the actual EVMYulLean MCOPY step, complete native poststate, original-memory snapshot copy (including overlap), and active-word extent. Full native ABI/prefix execution and context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceMcopyWindow` derives the exact native MCOPY destination carrier as original prefix, original source snapshot, and original suffix, including overlapping regions. Nonempty copy and both source/destination inside the existing memory carrier are explicit premises. Memory growth, outside-source behavior and complete native prefix equivalence remain open; CREATE2 admission stays closed.

`NativeSourceMcopyGrowth` proves growing native MCOPY carrier layout, original source-snapshot equivalence for any destination, and exact destination readback, including overlap. Nonempty in-carrier source, size<2^64 for readback and platform padding non-wraparound remain explicit. Native prefix input geometry, totality and context equivalence remain open; CREATE2 admission stays closed.

`NativeSourcePackingCopy` proves real pinned-runtime MCOPY decodes at PC647 and662 and derives exact source-snapshot readback from their actual native steps. Stack operands, successful step, in-carrier source and numeric size/padding conditions remain explicit; native prefix totality and context equivalence remain open. Decodes use bounded array lookup lemmas without raised Lean limits. CREATE2 admission stays closed.

`NativeSourcePackingStack` certifies actual opcodes at644–646 and executes their native DUP1/SWAP2/DUP10 sequence with exact gas debits, deriving first-MCOPY pop3 operands and unchanged memory. The incoming symbolic stack shape remains explicit; its derivation from earlier native instructions and full prefix/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourcePackingFragment` derives real sequential decodeAt values at644–646 from code identity and actual PC progression, then executes each native step to the exact prepared MCOPY stack. Incoming stack shape and per-step gas costs remain explicit; checked-runner gas sufficiency, preceding layout and complete native prefix/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceFirstCopy` executes real sequential decodeAt/native steps644–647 through the first MCOPY, deriving its operands and exact poststate, and proves destination readback equals the original source snapshot. Incoming stack, in-carrier source, size/padding conditions and per-step gas costs remain explicit; earlier native layout, checked-runner gas sufficiency and full context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceLoadStep` proves the exact native MLOAD state, stack result and preserved memory. Its value theorem retains both real lookupMemory guards: address within the existing carrier and not beyond the active-word limit. Earlier packing layout and full native prefix/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourcePreludeShuffles` executes the seven native SWAP5/DUP6/SWAP4/DUP4/DUP6/ADD/SWAP8 operations to an exact whole state, deriving the incoming length-load stack and preserving memory. Incoming symbolic stack, per-step cost and opcode sequence remain explicit; actual PC636–642 certificates and composition with adjacent MLOADs remain open. CREATE2 admission stays closed.

`NativeSourcePreludeLength` certifies actual runtime opcodes636–643 and composes the seven stack/arithmetic operations with native MLOAD, deriving its real lookupMemory value and complete resulting stack while preserving the memory carrier. Incoming symbolic stack, costs and operation sequence remain explicit; sequential decodeAt PC transport and earlier pointer/layout derivation remain open. CREATE2 admission stays closed.

`NativeSourcePreludeCopy` composes the seven-operation prelude and actual length MLOAD with real decoded steps644–647, deriving PC644, its stack and read length, then exact copied bytes from original memory. The earlier fixed-opcode sequence still needs sequential decodeAt transport; initial geometry, checked gas and full native/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourcePreludeDecoded` executes all eight real instructions636–643 through decodeAt at each computed PC, deriving the exact length-load state from initial code/PC/stack. A generic run-concatenation lemma preserves native errors. Incoming stack/geometry and per-step gas cost remain explicit; checked-runner gas sufficiency and full native/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceDecodedFirstCopy` executes the entire twelve-instruction real native fragment636–647 in one decodeAt-based runner, deriving the exact poststate after the first MCOPY. Initial stack/geometry and per-step gas cost remain explicit; preceding native input construction, checked gas sufficiency and full context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceFreePointer` certifies real632/633/635 decoding, including the actual PUSH1 immediate64 via a bounded one-byte extraction proof. It executes JUMPDEST/PUSH64/MLOAD to the real lookupMemory pointer, preserves memory and derives PC636. Sequential decodeAt transport for these three steps and complete native/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceDecodedPackingStart` executes all fifteen real instructions632–647 in one decodeAt-based runner, deriving the free pointer from native memory and the exact state after the first MCOPY. Initial PC632 stack and per-step gas cost remain explicit; derivation from contract entry, second copy and checked gas/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceSecondCopyHead` executes all nine real instructions648–656 through computed decodeAt/native steps, deriving the following MSTORE destination and value from the incoming stack while preserving memory. The stored value is not assumed zero; that property, connection to the first copy, layout and checked gas/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceSecondCopyStore` composes real decoded instructions648–658, including MSTORE657 at the derived destination/value and MLOAD658 from the resulting memory. Its seven laws retain the exact modified memory and loaded stack. Preservation of the original ABI source and literal window, value-zero derivation, connection to contract entry, second MCOPY and checked gas/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceSecondCopyShuffles` executes real decoded SWAP3/DUP4/SWAP2 at659–661 and derives MCOPY662 operands from its incoming four stack words, preserving memory. Its nine laws do not yet connect that entry stack to MLOAD658 or execute the second copy. Source geometry, contract-entry and checked gas/context obligations remain open; CREATE2 admission stays closed.

`NativeSourceSecondCopy` executes real decoded659–662 through the second MCOPY, deriving its operands and exact whole poststate. Four laws include source-snapshot byte readback under explicit source-carrier, positive-length and platform bounds. The incoming659 stack is still explicit; connection to MLOAD658, preservation across MSTORE657, contract-entry geometry and checked gas/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceSecondPacking` composes all fifteen real decoded instructions648–662, deriving the second MCOPY length from the actual MLOAD658 lookup in the post-MSTORE state. Its four laws include exact poststate and byte readback from that post-store snapshot under explicit bounds. It does not yet prove that MSTORE preserves the original ABI source or prefix, derive the incoming648 stack from the first copy, or establish contract-entry/checked-gas/context equivalence. CREATE2 admission stays closed.

`NativeSourcePackingCopies` composes all thirty real decoded instructions632–662 in one runner, deriving the entire648 stack and PC from the first copy before executing the second. Both lengths retain their actual native memory lookups; the MSTORE value is the original632 stack word g, not assumed zero. Contract-entry stack/layout, source/prefix memory frames, checked gas/context and invalid-input equivalence remain open. CREATE2 admission stays closed.

`NativeSourcePackingSize` executes actual decoded663–668 (ADD/ADD/DUP6/DUP2/MSTORE/SUB) with exact native state and derived store operands. Its thirteen laws keep the incoming eight-word stack explicit; connection to the preceding copies and the allocator call at680 remain open. The runtime jumps to910 and returns to681 before CREATE2; no linear663–685 execution is assumed. CREATE2 admission stays closed.

`NativeSourceSizedSecondCopy` derives the second-copy output stack and PC663, then composes real decoded648–668 including both MSTOREs and the actual MLOAD/MCOPY. Four laws retain the native length lookup and exact poststate. Incoming648 stack, original632 connection, allocator910 and contract-entry/layout/checked-gas obligations remain open; CREATE2 admission stays closed.

`NativeSourceSizedPacking` composes all thirty-six real decoded instructions632–668, including both MCOPYs and the subsequent size write, using a generic error-preserving concatenation lemma. Three laws retain exact native poststates and original632 stack premises. Allocation at910, original calldata geometry, memory frames, gas/context and invalid-input equivalence remain open; CREATE2 admission stays closed.

`NativeSourceRoundingEntry` certifies the actual669 PUSH1 immediate31 using a bounded byte extraction and composes it with real decoded671 NOT. Seven laws derive the exact native mask state while retaining the incoming stack. Subsequent rounding/store, allocator910 and full context/layout/gas equivalence remain open; CREATE2 admission stays closed.

`NativeSourceRoundingStore` executes real decoded672–675, deriving MSTORE destination and value from its incoming stack and retaining the exact modified memory. Nine laws keep the mask symbolic until connection to the actual669–671 prefix. The allocator call/return and full geometry/gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceRounding` composes all six real decoded instructions669–675, deriving the mask from the actual PUSH1/NOT before the size-header MSTORE. Four laws retain exact poststate and output stack. Connection to the original packing input and allocator910 call/return, geometry and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceRoundedSecondCopy` derives PC669 and the complete size stack from the actual second-copy/size-store result, then executes the native rounding store. Four laws compose real decoded648–675 without an assumed intermediate stack. Original632/contract-entry connection, allocator910, memory geometry and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceRoundedPacking` composes all forty-two real decoded instructions632–675 in one runner, including both copies, size write and rounding store, from the original632 stack. Two laws retain actual memory lookups and exact poststates. Allocator910 call/return, contract-entry geometry, memory frames and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorCall` certifies actual676 DUP3 and677 PUSH2, including bounded extraction of the two-byte910 immediate, and executes both instructions to the exact native pre-JUMP state. Six laws leave actual JUMP680, allocator checks/return and full geometry/context equivalence open. CREATE2 admission stays closed.

`NativeSourceAllocatorJump` executes actual decoded676–680 through JUMP910, deriving the target and exact allocator-entry stack from the real DUP3/PUSH2 preparation. Five laws retain full native step state. This step runner does not check metered jump validity or sufficient gas; allocator branches/return and contract-entry geometry remain open. CREATE2 admission stays closed.

`NativeSourceAllocatorStart` executes the actual allocator entry910–912 (JUMPDEST/SWAP1/PUSH31), including exact immediate extraction and computed decodeAt steps. Eight laws retain the symbolic incoming stack and full native poststate. Allocation arithmetic, overflow branch and return, connection to the packing entry, and checked gas/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceAllocatorRounding` executes actual decoded914–918, deriving the exact modular `(size + word) AND NOT word` stack and preserving memory. Thirteen laws keep the incoming word explicit pending connection to the real PUSH31 entry. No no-overflow premise or natural-number rounding equality is assumed. Allocation guards/return and full geometry/context/gas equivalence remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorRoundedEntry` executes all eight real decoded instructions910–918 from the allocator entry, deriving the mask from the actual PUSH31 and the exact modular rounded-size stack. Four laws avoid an assumed intermediate word or success. Allocation overflow checks/return, caller connection and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorPointer` executes real decoded919–923, deriving the modular new free pointer and native unsigned LT overflow-test word, preserving memory. Thirteen laws retain the incoming size/base stack and exact state; no no-overflow result is assumed. The 64-bit limit check, failure branch/return, caller connection and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorOverflowEntry` composes all thirteen real decoded instructions910–923, deriving the modular new pointer and overflow-test word from the allocator entry and actual PUSH31. Four laws preserve exact state without assuming guard success. The 64-bit limit and failure branch/return, caller geometry and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorLimit` certifies the exact eight-byte max64 immediate and executes actual decoded924–935 (PUSH8/DUP3/GT/OR), deriving the combined native overflow/limit-test word. Twelve laws retain both failure causes and the full poststate; no successful guard is assumed. Conditional branch, allocation write/return, caller geometry and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorGuard` executes all seventeen real decoded instructions910–935, deriving both allocation failure tests and their combined native word from the original allocator stack. Four laws retain exact poststates without a guard-success assumption. Conditional branch/return, caller geometry and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorBranch` certifies the actual PUSH2 immediate786 and executes real decoded936/939 to an exact native conditional poststate. Seven laws derive both destinations:786 when the guard word is nonzero and940 otherwise. No successful branch is assumed; allocator write/return, panic payload, caller geometry and checked gas/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceAllocatorDecision` composes all nineteen real decoded instructions910–939 from the allocator input, deriving the actual overflow/limit flag and both branch destinations. Four laws keep exact conditional poststates without a success assumption. Allocation write/return, failure payload, caller geometry and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorReturn` executes real decoded940–943, storing the actual stack pointer at memory64 and jumping to the actual stack return word. Nine laws include exact PUSH64 extraction and full poststates. Connection to the successful allocator decision, failure panic payload, return681 derivation, caller geometry and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorSuccess` composes all twenty-two real native allocator instructions from910 through943 on the explicitly computed guard-zero path, deriving the write and stack-supplied return target. Six laws retain exact poststates; the guard is not yet derived from caller geometry and the return address is not assumed681. Failure panic, caller connection and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorGuardZero` proves the actual combined native guard is zero from explicit new-pointer bounds (at most max64 and at least the original base), with a bridge from natural-number observations. Two laws do not derive those bounds from caller allocation geometry. The success execution remains conditional on such bounds; failure panic and full context/gas equivalence remain open. CREATE2 admission stays closed.

`NativeSourceAllocatorCaller` composes actual676–680 with all twenty-two native allocator success instructions, deriving base, size and return address from the caller stack. Four laws retain exact poststate and returned stack under the explicit computed guard-zero condition. Connection to packing632–675, caller bounds, failure panic and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourcePackedAllocation` derives the allocator caller PC676 and stack from the actual second-copy/size/rounding execution, composing fifty-two real decoded instructions from648 through allocator return. Four laws retain an explicit computed guard-zero condition; return target is the incoming stack word f. The original632 connection, return681/guard derivation, memory geometry, failure panic and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceOriginalAllocation` composes sixty-seven real native instructions from632 through both copies and allocator return. Four laws derive the return target as the original632 word d and the returned stack from the original memory-loaded free pointer. The computed guard-zero condition remains explicit; deriving d=681 and bounds from contract entry, failure panic, memory frames and checked gas/context equivalence remain open. CREATE2 admission stays closed.

`NativeSourceCreateOperands` executes real decoded681–684 and derives the exact following CREATE2 pop4, including the length from actual MLOAD and repeated stack value. Ten laws keep the incoming stack explicit; connection to allocator return, zero-value/salt and canonical initcode geometry are not assumed. CREATE2 admission stays closed pending full context/gas and invalid-input equivalence.

`NativeSourcePreCreate` composes seventy-one real native instructions from632 through the allocator and681–684, deriving exact CREATE2 operands from the original632 stack and native length lookup. Three laws keep original return-word681 and computed guard-zero conditions explicit. Contract-entry derivation, zero value/salt, canonical initcode, failure panic and checked gas/context equivalence remain open; CREATE2 admission stays closed.

`NativeSourceZeroShuffles` executes actual decoded573–578 from the real PUSH0 through four SWAPs and DUP2, preserving memory and tracking the introduced zero in the derived stack. Fifteen laws keep the incoming573 stack explicit; subsequent return-address pushes, ABI writes, first allocator and contract-entry connection remain open. CREATE2 admission stays closed.

`NativeSourceReturnConstants` certifies the actual579 PUSH32,582 PUSH681 and587 PUSH632 decodes with bounded extraction of each real immediate. Six laws establish constant provenance; execution and propagation through the surrounding stack permutations remain open, as do the earlier ABI context and checked gas/layout equivalence. CREATE2 admission stays closed.

`NativeSourceReturnShuffles` executes all seven real decoded instructions579–590, propagating actual32/681/632 constants through SWAP8/SWAP11 with exact native stack and memory preserved. Fourteen laws keep the incoming579 stack explicit; connection to PUSH0, ABI field writes and the first allocator remains open. CREATE2 admission stays closed pending full context/layout/gas equivalence.

`NativeSourcePackingContext` composes the thirteen actual decoded instructions573–590, deriving the introduced zero and both return constants632/681 jointly from the explicit573 input stack. Four bounded laws certify the exact native state through entry591. ABI field writes, the first allocator, geometry, gas and contract-entry equivalence remain open; CREATE2 admission stays closed.

`NativeSourceFieldLoad` connects actual MLOAD591 to the derived573–590 context in fourteen native instructions. Seven bounded laws retain the actual pre-MLOAD memory lookup, including native active-memory behavior. Subsequent ABI field writes, allocator geometry, gas and entry equivalence remain open; CREATE2 admission stays closed.

`NativeSourceFieldStore` proves the four actual instructions592–596: PUSH192, DUP9, ADD and MSTORE. Ten bounded laws derive the native write address `h + 192` and stored input word from the explicit592 stack, retaining full native memory and active extent. Connection to the preceding MLOAD, remaining field writes, layout, allocator bounds and gas remains open; CREATE2 admission stays closed.

`NativeSourceFirstField` connects the first ABI field write to the actual573 context: eighteen native instructions through596, with the word read by MLOAD591 written at original `c + 192`. Four bounded laws derive the successor stack and retain the exact native state. Original573 inputs, subsequent fields, allocator bounds, canonical layout, gas and contract entry remain obligations; CREATE2 admission stays closed.

`NativeSourceSecondFieldStore` proves the four actual instructions598–602: PUSH224, DUP8, ADD and MSTORE, deriving address `g + 224` and stored word from the explicit598 stack. Ten bounded laws retain the native whole state; preceding MLOAD597 and full context, subsequent fields, canonical layout, bounds and gas remain open. CREATE2 admission stays closed.

`NativeSourceSecondFieldLoad` connects actual MLOAD597 to the eighteen-instruction context through the first ABI write. Six bounded laws execute nineteen native instructions from573 and retain lookup of original `e` in the actual post-first-write state. Connection to the second store, subsequent fields, canonical layout, bounds, gas and contract entry remain open; CREATE2 admission stays closed.

`NativeSourceSecondField` composes twenty-three actual instructions573–602 through both native field loads and stores. Four bounded laws derive the second write at original `c + 224`, reading original `e` from the actual post-first-write memory; exact native state and successor stack are retained. Masked fields, canonical layout, allocator bounds, gas and contract entry remain open; CREATE2 admission stays closed.

`NativeSourceMaskedFieldLoad` proves actual MLOAD603 and AND604 with five bounded laws. The native load uses the actual pre-MLOAD memory and active extent, then bitwise AND applies the explicit stack mask. Full context, mask provenance, following stores, canonical layout, bounds and gas remain open; CREATE2 admission stays closed.

`NativeSourceMaskedContext` connects twenty-five actual instructions573–604, deriving the mask from original stack word `a` and reading original `f` in the actual post-second-write memory. Four bounded laws retain exact native state and stack. The numerical mask provenance before573, later stores, canonical layout, allocator bounds, gas and contract entry remain obligations; CREATE2 admission stays closed.

`NativeSourceMaskedFieldStore` proves the four actual instructions605–610, including the exact two-byte PUSH256 immediate, DUP6, ADD and native MSTORE. Ten bounded laws derive address `e + 256` and stored input word from the explicit605 stack. Connection to masked context, remaining fields, canonical layout, bounds and gas remain open; CREATE2 admission stays closed.

`NativeSourceThirdField` composes twenty-nine actual instructions573–610 through the third field write. Four bounded laws derive the native write at original `c + 256`, storing actual post-second-write lookup of original `f` bitwise AND original `a`. Original573 inputs and mask provenance, fourth field, canonical layout, bounds, gas and entry remain obligations; CREATE2 admission stays closed.

`NativeSourceFourthFieldLoad` proves actual MLOAD611 and AND612 with five bounded laws, retaining the actual pre-MLOAD lookup and explicit stack mask. Connection to the third-write context and fourth field store, canonical layout, allocator bounds, gas and contract entry remain open; CREATE2 admission stays closed.

`NativeSourceFourthContext` composes thirty-one actual instructions573–612 through the fourth field load and mask. Four bounded laws derive the lookup of original `g` in actual post-third-write memory, masked by original `a`, with exact native state and stack. Fourth store, numerical mask provenance, canonical layout, bounds, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceFourthFieldStore` proves actual613–618 with ten bounded laws: exact PUSH288 immediate, DUP4, ADD and native MSTORE, deriving generic address `c + 288` and the stored word from the explicit613 stack. Full context connection, size calculation, canonical layout, bounds, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceFourthField` composes thirty-five actual instructions573–618 through all four native field writes. Four bounded laws derive the last write at original `c + 288` from the actual post-third-write lookup of original `g` masked by original `a`, retaining exact native state and successor stack. Original573 inputs, mask provenance, size calculation, canonical layout, bounds, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceFieldSizeEntry` proves native SUB619 and exact PUSH31 immediate/decode at620 with four bounded laws. Subtraction retains native modular word semantics. Full size execution, original context connection, allocation bounds, canonical layout, gas and entry remain obligations; CREATE2 admission stays closed.

`NativeSourceFieldRoundingEntry` proves actual PUSH31 at620 and NOT622, including exact immediate bytes and both native steps, in seven bounded laws. Full size/store/context composition, allocation bounds, canonical layout, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceFieldRoundingStore` proves actual623–626 in nine bounded laws: DUP2, ADD, DUP8 and MSTORE retain the native state, deriving the stored word `size + mask` and write address from the explicit623 stack. Full size/context composition, canonical layout, allocator bounds, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceFieldSize` composes the seven actual instructions619–626 with four bounded laws, preserving native modular subtraction, bitwise NOT and ADD, stack-derived write address and exact MSTORE state. Connection to the original573 context, allocation bounds, canonical layout, gas and entry remain obligations; CREATE2 admission stays closed.

`NativeSourceSizedFields` composes forty-two actual instructions573–626 through four field writes and size calculation. Four bounded laws retain exact native state and derive the stack before627, including size `b - c`, return632, later return681 and the PUSH0 word. Original573 inputs, mask provenance, allocator bounds, canonical layout, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceFirstAllocatorCall` proves actual DUP7 at627 and PUSH910 at628 in six bounded laws, including exact immediate bytes and native whole states. The stack-derived allocator arguments are retained; JUMP631, original573 context connection, allocator bounds, layout, gas and entry remain open. CREATE2 admission stays closed.

`NativeSourceFirstAllocatorJump` proves the actual JUMP631 and three-instruction call sequence from627, deriving entry910 and its stack in five bounded laws. Allocator success guard, original573 context connection, metered jump validity, canonical layout, bounds, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceFirstAllocatorCaller` connects actual627–631 to the twenty-two allocator success instructions, with four bounded laws and explicit computed guard zero. The return target and remaining stack are derived from the actual caller stack. Original573 context, guard bounds, canonical layout, gas, metered jump validity and entry remain open; CREATE2 admission stays closed.

`NativeSourceFieldsAllocation` composes sixty-seven actual instructions from573 through the first allocator return632. Five bounded laws derive the returned stack, including return681 and the PUSH0 word, under the explicit computed guard for original `j` and `b - c`. Original573 inputs, guard bounds, canonical initcode, gas, metered jumps and entry remain obligations; CREATE2 admission stays closed.

`NativeSourceContextPreCreate` composes 138 actual native instructions from573 through the state before CREATE2 at685. Three bounded laws derive both CREATE2 value and salt as zero from actual PUSH0 and the native stack, eliminating separate681/zero assumptions. Both allocator guards remain explicit; original573 inputs, canonical initcode, bounds, gas, metered jump validity, entry and invalid-input equivalence remain open. CREATE2 admission stays closed.

`NativeSourceMemoryFrame` supplies three bounded native memory lemmas: disjoint reads below/above a fitting MSTORE, and lookup transport with explicit carrier and active-memory guards on both states. Actual geometry, growing writes, canonical initcode, allocation bounds, gas and entry remain obligations. No memory oracle or CREATE2 admission is introduced.

`NativeSourceGrowingFrame` proves preservation of an existing read window below a growing native MSTORE. The bounded lemma retains the explicit platform padding bound, original read bounds and disjointness; actual geometry and active-memory lookup guards must still be established at callers. Canonical initcode, allocator bounds, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceStoreFrame` unifies fitting and growing MSTORE lower-window frames and derives native lookup preservation in two bounded laws. Platform padding bounds, original read bounds, disjointness and before/after active guards remain explicit. Actual field geometry, canonical initcode, allocator bounds, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceFirstFieldFrame` applies native lower-window preservation to all four actual ABI field-store whole states, in four bounded laws. Actual modular write addresses at offsets192/224/256/288, platform padding bounds and original read geometry remain explicit. Composition, active guards, canonical initcode, allocation bounds, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceFieldMemorySize` derives exact carrier size and monotonicity for all four actual ABI field-store whole states, in eight bounded laws. Each size is the maximum of the original carrier and actual modular write address plus32, under the explicit platform padding bound. Actual geometry, active extent, canonical initcode, allocator bounds, gas and entry remain open; CREATE2 admission stays closed.

`NativeSourceContextFieldFrames` connects lower-window preservation to all four actual field states derived from573, in five bounded laws including the prefix memory equality. Each transition keeps actual modular write geometry and platform padding bounds explicit. Full composition, entry geometry, active guards, canonical initcode, allocation bounds and gas remain open; CREATE2 admission stays closed.

`NativeSourceAllFieldsFrame` composes all four actual573-derived field frames into preservation of an original lower read window through618. The bounded law retains each intermediate padding bound, carrier bound and disjointness condition. Discharging those bounds from entry geometry, active guards, canonical initcode, allocator bounds and gas remains open; CREATE2 admission stays closed.

`NativeSourceContextMemorySize` connects carrier monotonicity to all four actual field states derived from573, in four bounded laws with explicit platform padding bounds. Intermediate read-carrier bounds can therefore follow from the original bound. Active guards, entry geometry, canonical initcode, allocator bounds and gas remain open; CREATE2 admission stays closed.

`NativeSourceOriginalWindowFrame` derives all intermediate read-carrier bounds by actual context monotonicity, preserving the original lower window through all four field writes using only the original inside bound. Padding and disjointness remain explicit at each actual address. Entry geometry, active guards, subsequent size/allocator writes, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceSizeMemoryFrame` preserves an existing lower read window across the exact619..626 size store, in six bounded laws. Intermediate memory equalities avoid reducing the entire composed state in the kernel. Actual write address, padding and disjointness remain explicit; entry geometry, allocator/MCOPY frames, canonical initcode and gas remain open. CREATE2 admission stays closed.

`NativeSourceContextSizeFrame` connects the lower-window size-store frame to the actual573-derived ABI context through626. The store address is the original stack word `j`, derived by the execution proof; padding, disjointness and the read-carrier bound remain explicit. Canonical initcode, entry geometry, allocator/MCOPY frames and gas remain open; CREATE2 admission stays closed.

`NativeSourceSizedWindowFrame` composes the four field stores and size store through626, preserving an original lower memory window with intermediate carrier bounds derived from actual memory monotonicity. Padding and disjointness remain explicit; entry geometry, allocator/MCOPY frames, canonical initcode and gas remain open. CREATE2 admission stays closed.

`NativeSourceAllocatorReturnFrame` proves that the actual allocator pointer MSTORE at64 and return preserve existing read windows starting at96 or above, in three bounded laws. The write-fit bound follows from window geometry. Allocator-prefix memory transport, entry geometry, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceAllocatorPrefixMemory` proves memory identity across the actual allocator rounding, overflow checks and branch, then composes the pointer-store frame for the complete success return. Ten bounded laws preserve existing windows beginning at96 or above. Caller transport, entry geometry, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceFirstAllocatorFrame` transports memory preservation through the actual627/628/631 allocator call and the original573-derived return632, in three bounded laws. Existing windows starting at96 or above survive the pointer write. Entry geometry, MCOPY source frames, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceSizeCarrier` derives exact carrier size and monotonicity across the size store619..626 and its actual573 context, in four bounded laws. The native platform padding bound remains explicit. This supplies intermediate read-carrier bounds for allocator frame composition; entry geometry, canonical initcode and gas remain open. CREATE2 admission stays closed.

`NativeSourceAllocatedWindowFrame` preserves an original memory window through the actual573 field stores, size store and first allocator return632. All intermediate carrier bounds follow from original containment and native monotonicity; padding, disjointness and start>=96 remain explicit. MCOPY frames, canonical initcode, entry geometry and gas remain open; CREATE2 admission stays closed.

`NativeSourceCopyProvenance` transports a preserved source read window to its original byte extract, then proves MCOPY destination readback equals that original extract. Both bounded laws retain containment, positive length, native size bound and padding conditions; overlap uses the native snapshot semantics. Actual copy contexts, entry geometry, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceFirstCopyProvenance` relates both actual MCOPY whole states at647/662 to native snapshot writes and original-source destination readback, in five bounded laws. Source preservation, containment and padding remain explicit. Deriving these conditions from entry, preserving copied windows through later writes, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceCopyWindowFrame` proves disjoint lower/upper window preservation for fitting native snapshot copies and lower-window preservation for growing copies, with a unified lower frame. Four bounded laws retain source containment and platform padding conditions. Actual context geometry, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceActualCopyFrames` applies lower-window preservation to both exact native copy whole states647/662, for fitting or growing memory. Two bounded laws keep positive copy length, source containment, platform padding and window geometry explicit. Empty copies, entry geometry, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceEmptyCopy` proves zero-length native write identity and memory identity for both actual empty-copy whole states647/662, in three bounded laws. This removes the need to assume positive dynamic copy length in composed memory frames. Context geometry, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceTotalCopyFrame` unifies empty and positive copy lengths for native lower-window preservation and both actual copy whole states647/662, in three bounded laws. Source containment, padding and window geometry remain explicit. Entry geometry, intermediate stores, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceIntercopyStoreFrame` preserves existing lower windows through actual657 MSTORE and658 MLOAD, with five bounded memory laws. The exact modular write address is `(e + length) + d`; padding, containment and disjointness remain explicit. Canonical initcode, entry geometry and gas remain open; CREATE2 admission stays closed.

`NativeSourceIntercopyCarrier` derives exact memory size and monotonicity after657 MSTORE and exact size after658 MLOAD, in three bounded laws. Platform padding remains explicit; these facts derive intermediate containment for the second-copy frame. Entry geometry, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceSecondPackingFrame` composes lower-window preservation through657 MSTORE,658 MLOAD and662 MCOPY, including empty copies. Two bounded laws derive intermediate containment and copy padding from native carrier size. Source containment and actual address geometry remain explicit; canonical initcode, entry and gas remain open. CREATE2 admission stays closed.

`NativeSourceFirstPayloadSurvival` proves the first647 copy payload remains equal to its original source after657store/658load/662copy. A second bounded law derives exact first-copy carrier size, removing intermediate destination containment as an assumption. Source containment, padding and address geometry remain explicit; entry, canonical initcode and gas remain open. CREATE2 admission stays closed.

`NativeSourceFinalRoundingFrame` proves upper-window preservation through actual675 MSTORE and full669..675 rounding, with four bounded laws. The write-fit condition is derived from original window containment and disjointness. Entry geometry, second allocator, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceSizedPackingMemory` retains the actual667 MSTORE in663..668 size computation and proves its exact native memory effect and lower-window frame. Two bounded laws keep actual modular address, padding and disjointness explicit. Canonical initcode, entry geometry and gas remain open; CREATE2 admission stays closed.

`NativeSourceFinalSizeContext` connects the actual667 store to its packing context, proves exact carrier size, and composes window preservation through667 and675. Three bounded laws derive intermediate containment while retaining actual address geometry and padding. Second allocator transport, canonical initcode, entry and gas remain open; CREATE2 admission stays closed.

`NativeSourceSecondAllocatorFrame` transports upper-window preservation through the actual second allocator call and packed-allocation return, in three bounded laws. Existing windows starting at96 or above survive the pointer write. Context geometry, canonical initcode, entry and gas remain open; CREATE2 admission stays closed.

`NativeSourceRoundedCarrier` proves exact675store/fullrounding/context carrier sizes and derives unchanged carrier from existing upper-window geometry, in four bounded laws. This supplies containment for second-allocator frame composition. Canonical initcode, entry geometry and gas remain open; CREATE2 admission stays closed.

`NativeSourcePackedReturnFrame` composes window preservation across667/675 and the second allocator, deriving intermediate containment, and proves memory identity for681..684 CREATE2 operand preparation. Two bounded laws retain actual geometry. Canonical initcode, entry and gas remain open; CREATE2 admission stays closed.

`NativeSourcePayloadReturn` composes first-payload provenance through both copies, intermediate stores and second allocator return. Three bounded laws derive native copy/second-packing carrier monotonicity and remove final containment as an assumption. Source geometry, canonical ABI/initcode, entry and gas remain open; CREATE2 admission stays closed.

`NativeSourcePreCreateMemory` transports exact memory from the original allocator return through681..684 to the pre-CREATE2 state. The bounded law retains the native MLOAD and stack operations. Payload geometry, canonical initcode, entry and gas remain open; CREATE2 admission stays closed.

`NativeSourceSecondPayload` proves actual662 destination readback equals the original source extract, using the actual post657 length lookup. Copy padding follows from native657 carrier size. Source preservation, positive length and geometry remain explicit; canonical initcode, entry and gas remain open. CREATE2 admission stays closed.

`NativeSourceSecondSourceFrame` derives second-copy source preservation through657store/658load from actual disjointness and containment, then proves destination readback equals the pre657 source extract. The bounded law derives intermediate containment. Full return transport, canonical initcode, entry and gas remain open; CREATE2 admission stays closed.

`NativeSourceSecondPayloadReturn` transports the second payload from pre657 source memory through667/675 and the second allocator return, deriving destination containment from the native copy size. Two bounded laws retain source geometry and actual post657 length. Empty payloads, canonical initcode, entry and gas remain open; CREATE2 admission stays closed.

`NativeSourceEmptyPayload` proves zero-length read/extract identities and empty second-payload provenance at allocator return, in three bounded laws without address geometry assumptions. Unifying payload lengths, canonical initcode, entry and gas remain open; CREATE2 admission stays closed.

`NativeSourceTotalSecondPayload` unifies empty and positive second-payload provenance at allocator return, without a positivity assumption. The bounded law retains actual post657 length and geometry. Deriving geometry from entry, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceAddressGeometry` proves native256-bit addition agrees with natural addition under a nonwrap bound and derives the second payload end bound from a single final-sum bound. Two bounded laws retain modular semantics. Entry-derived bounds, canonical initcode and gas remain open; CREATE2 admission stays closed.

`NativeSourceBoundedSecondPayload.readback_return` derives the second payload
final bound from an explicit nonwrapping natural address sum, using native
UInt256 geometry. Source containment, padding and disjointness remain explicit;
actual entry geometry, canonical initcode and CREATE2 admission remain unproved.

`NativeSourceTotalFirstPayload.readback` extends first-payload provenance to
zero length using exact empty native reads and extracts. Nonempty cases retain
the existing source, frame and allocator premises. This does not establish
canonical initcode or authorize CREATE2.

`NativeSourceBoundedFirstPayload.readback` derives the first payload final
bound from its position below the second output and an explicit nonwrapping
end-address sum. Actual entry bounds and canonical initcode remain unproved;
CREATE2 admission remains closed.

`NativeSourceDecodedCopyProvenance` connects the first native copy to the
actual state after instruction 632, including empty payloads. Its length is
the lookup after loading the free pointer: MLOAD changes activeWords even
when memory bytes remain equal. Source containment and copy padding remain
explicit; this establishes neither canonical initcode nor CREATE2 admission.

`NativeSourceActiveLength` proves that loading the free pointer at address64
preserves activeWords when at least three words are already active. Length
lookup transport then needs only the original active guard and carrier bound.
These entry conditions must still be derived for the full runtime proof.

`NativeSourcePointerActive` derives at least three active words from the native
allocator pointer store at address64, through allocator success, first caller
and actual FieldsAllocation return632. No entry assumption is needed for this
extent bound; carrier/source guards and canonical initcode remain obligations.

`NativeSourceContextLength.lookup` transports the actual632 length lookup
using the allocator-derived active extent; only the original carrier and active
guard remain premises. Their connection to entry decoding is still open.

`NativeSourceContextCopy` specializes the first copy to the actual return632
stack, splitting one tail element for the eighth argument. It proves execution,
length lookup and all-length readback at the actual free-pointer-plus32 output.
Source containment, padding and lookup guards still require entry proofs.

`NativeSourceAllocatorCarrier` proves exact carrier-size preservation through
allocator return, success, first caller and actual return632 when the pointer
store fits in the carrier (at least96 bytes). Active extent remains separate.

`NativeSourceContextOriginalCopy.readback` proves actual first-copy bytes equal
the original573 source extract, including zero length. Intermediate source
containment follows from native store growth and allocator carrier preservation.
The five-store frame and copy padding conditions still require entry geometry.

`NativeSourceFieldGeometry` derives the later field-frame lower bounds from
the first field and one nonwrapping end offset, and establishes contiguous
payload boundaries under a nonwrapping sum. Actual entry bounds remain open.

`NativeSourceGeometricOriginalCopy.readback` derives the three later field
frame bounds from the first field bound and one nonwrap condition. Padding,
original source containment and entry geometry remain explicit obligations.

`NativeSourceFieldPadding` derives the next three field-store padding bounds
from the first store padding and nonwrapping field geometry. Each consecutive
address is contained in the carrier produced by its predecessor. Original
source and entry geometry, final size-store and copy padding remain open.

`NativeSourceDerivedPaddingCopy.readback` removes the three intermediate
field padding premises from original573 provenance. They follow from native
store carrier growth and nonwrapping field geometry. First-store, size-store
and copy padding, source containment and entry geometry remain premises.

`NativeSourceSizePadding` derives the size-word padding from the first field
store padding, nonwrapping field geometry and the size-word address below the
fourth-store extent. The original entry geometry and copy padding remain open.

`NativeSourceSizedPaddingCopy.readback` derives size-word padding from its
address below the fourth-store extent; the copy provenance theorem now needs
only first-store and copy padding. Actual size-word geometry remains a premise.

`NativeSourceBoundedPadding` derives first-store and copy padding from absolute
address bounds, preserving modular nonwrap conditions. Actual entry and allocator
bounds must still be proved before CREATE2 admission.

`NativeSourceAllocatorAcceptedBounds` derives the two comparison checks from
the actual zero allocator flag and proves the natural base-plus-rounded-amount
sum is below2^64. The native overflow check rules out modular wrap. Rounding
size relationships and actual caller guard derivation remain proof obligations.

`NativeSourceAllocatorMargin` derives base and interior-address bounds from
the actual accepted allocator flag. Copy padding follows with rounded margin
of at least32 and explicit platform width at least64; these conditions remain
obligations for actual callers. No platform equality is assumed by the kernel.

`NativeSourceRoundingArithmetic` proves the allocator mask equals
`((size + 31) / 32) * 32` when the natural addition does not wrap. It covers
the requested size and gives at least32 bytes for a positive size. The
nonwrapping addition condition remains an actual-entry proof obligation.

`NativeSourceRequestedMargin` derives natural requested-end bounds and
copy/field padding from the accepted allocator guard and requested size,
using proven rounding. Nonwrapping size+31 and platform width remain explicit.

`NativeSourcePointerBytes` proves native stored-word bytes and transports
allocator pointer bytes through the actual first caller and return632. At64
the bytes equal `(j + amount (b - c)).toByteArray`. Converting this byte fact
to an active-guarded lookup and discharging entry padding remain obligations.

`NativeSourceWordRoundtrip` proves fixed-byte decoding and native UInt256
word roundtrip, then exact lookup from known bytes under both native carrier
and active-word guards. No active-extent guard is silently discarded.

`NativeSourcePointerLookup` derives the pointer carrier from native MSTORE64,
then recovers the allocator pointer with exact native lookup through actual
FieldsAllocation return632. Store padding and the active-word multiplication
guard remain explicit obligations; these lemmas do not admit CREATE2.

`NativeSourceContextFree` identifies the actual return632 free pointer as
`j + amount (b - c)` using the native lookup lemmas. Pointer-store padding
and active-extent guards remain hypotheses; CREATE2 admission remains closed.

`NativeSourcePointerExtent` derives the pointer lookup active guard from
allocated words at least three and strictly below 2^251, proving multiplication
by 32 does not wrap. Actual return632 allocation supplies the lower bound.
The upper bound and store padding still require entry derivation.

`NativeSourceAllocatorExtent` proves active-word preservation through the
allocator decision prefix and first-caller entry. The actual return632 extent
is exactly `max` of the pre-allocator extent and three; its upper bound now
follows from the pre-allocator bound. Entry bounds remain to be established.

`NativeSourcePreallocatorFree` derives actual return632 free from the
pre-allocator extent bound, using the proved allocator max extent. The bound
after field stores and pointer padding remain obligations; CREATE2 stays closed.

`NativeSourceWordAccessExtent` proves native MLOAD/MSTORE preserve the
active-word bound below 2^251 when the accessed address is below 2^64.
Concrete field access bounds and initial extent remain entry obligations.

`NativeSourceFirstFieldExtent` transports the active-word bound through
actual field preparation, source MLOAD and first MSTORE. Initial extent,
source address and destination address bounds remain explicit obligations.

`NativeSourceSecondFieldExtent` transports the active-word bound through
the actual second-field source MLOAD and MSTORE at c+224. The incoming
extent and both accessed address bounds remain explicit obligations.

`NativeSourceThirdFieldExtent` transports the active-word bound through
the actual third-field masked source load and MSTORE at c+256. Incoming
extent and both accessed address bounds remain explicit obligations.

`NativeSourceFourthFieldExtent` transports the active-word bound through
the actual fourth masked source load and native MSTORE at c+288. Incoming
extent and source/destination bounds remain explicit obligations.

`NativeSourceSizeFieldExtent` proves the sizeword MSTORE extent via
scalar active-word equations, and composes all four source loads plus five
stores from original573. Initial active extent and concrete access address
bounds remain hypotheses; canonical initcode and CREATE2 admission stay open.

`NativeSourceOriginalFree` identifies the actual return632 free pointer
from original573 extent and concrete access bounds, deriving allocator
active guards and pointer padding. The platform bound (at least seven bits)
is explicit; concrete entry bounds and canonical initcode remain open.

`NativeSourceFieldAddressBounds` derives all four native field destination
bounds from the single natural bound c+288 below 2^64, including nonwrap.
The natural bound must still follow from actual entry geometry.

`NativeSourceGeometricFree` identifies actual return632 free with one
natural destination bound c+288, deriving all four native access bounds.
An accepted allocator with nonwrapping size+31 and requested size at least
288 supplies that bound. Actual entry/caller hypotheses remain obligations.

`NativeSourceAcceptedFree` bounds actual return632 free below 2^64
under the accepted allocator guard and original entry bounds. The sizeword
address bound follows from the guard; original source/extent/field geometry
and actual guard derivation remain obligations.

`NativeSourceAllocatorPaddingCopy` derives first-field and copy padding
for all-length original573 source readback, from natural field geometry,
platform>=64 and accepted allocator conditions at actual free. Concrete
second-caller guard/requested-size derivation remains open.

`NativeSourceRequestedGeometry` proves exact natural subtraction under
ordered operands and exact requested size for nonwrapping end geometry.
Concrete PackedAllocation operands and entry bounds remain obligations.

`NativeSourcePackedRequested` proves the natural value, positivity and
rounding nonwrap of actual PackedAllocation.size and derives copy padding
from its native allocator guard. Natural end/gap and actual caller operand
provenance remain obligations; CREATE2 admission remains closed.

`NativeSourceContextPacked` connects the actual first-copy stack to the
second PackedAllocation operands (base free, gap32) and derives padding
from its exact requested size and guard. End bounds/guard derivation and
canonical initcode remain obligations.

`NativeSourceContextPaddingReadback` proves original573 first-payload
readback using exact context second-allocator operands, deriving both
padding requirements. Entry/end/guard, source and disjointness conditions
remain explicit; final payload survival and CREATE2 admission remain open.

`NativeSourceCopiedPayloadReturn` preserves an already copied payload
through second packing, final sizeword MSTORE and allocator return, for
all lengths including zero. Concrete containment, disjointness, padding
and final extent remain obligations; CREATE2 stays closed.

`NativeSourceFirstOutputGeometry` proves exact base+32 destination
geometry, allocator-word separation and first-payload boundary below the
second copy under natural nonwrap bounds. Concrete entry bounds and
canonical initcode remain obligations.

`NativeSourceGeometricPayloadReturn` derives the four payload position
conditions for destination base+32 from base>=64 and natural end nonwrap.
Memory containment, second-source bounds and padding remain obligations.

`NativeSourceContextPayloadReturn` specializes payload preservation to
the actual original573/632 firstcopy and secondallocator operands. Source
and destination containment, end bounds and later padding remain explicit.

`NativeSourceOriginalPayloadReturn` composes actual firstcopy provenance
and packed-return preservation: the returned first payload equals the
original573 source extract for every length. Entry geometry, containment,
padding and guards remain hypotheses; canonical initcode remains open.

`NativeSourceBoundedOriginalReturn` derives preservation nonwrap from
the actual end+31 bound, removing a duplicate end hypothesis from original
first-payload return. Entry/memory/guard and canonical-initcode obligations
remain open.

`NativeSourceTotalOriginalReturn` requires copied-destination containment
only for positive lengths; zero reads/extracts are proved empty directly.
The exact all-length returned payload conclusion is unchanged.

`NativeSourcePreludeCopySize` proves exact positive-length firstcopy
carrier size through the decoded preamble, with source containment and
padding explicit. Zero-length MCOPY expansion is not asserted.

`NativeSourceContextCopySize` derives exact positive firstcopy carrier
size and destination containment in the actual context. Source containment
and padding remain explicit, and zero-copy expansion is not asserted.

`NativeSourceContainedOriginalReturn` derives positive destination
containment from actual firstcopy size and allocator padding. Original
and returned source containment still require proof from entry geometry.

`NativeSourceContextSourceInside` transports original source containment
through all five field stores and allocator carrier equality, deriving
intermediate paddings from first padding and sizeword geometry.

`NativeSourceOriginalContainedReturn` derives both intermediate source
and destination containment for exact original573 returned first payload.
Original containment, entry geometry, allocator guards and later padding
remain obligations; canonical initcode remains open.

`NativeSourcePackedEndBound` derives final natural end below 2^64 and
final sizeword padding from actual PackedAllocation guard and end+31
nonwrap. Exact native finish geometry is proved; entry guards remain open.

`NativeSourceGuardedOriginalReturn` derives both remaining later padding
conditions from the exact second allocator guard/end bound. Exact original
first-payload return retains source, geometry and actual guard obligations.

`NativeSourceSecondSourceContainment` derives pre-MCOPY source
containment through the intercopy MSTORE carrier growth, including a
variant using a bound on the actual native length lookup. Original source
and length provenance remain obligations.

`NativeSourceLookupFrame` transports exact native word lookup across
equal bytes with explicit carrier and active guards, and applies it to
the real intercopy MSTORE. Active-extent guards must still be derived.

`NativeSourceStoreActiveGuard` proves bounded MSTORE active extent
monotonicity, exact active-byte product and preservation of native read
guards, without assuming carrier equality implies equal lookup.

`NativeSourceIntercopyActiveLookup` derives the post-MSTORE active
guard and preserves actual second-source length lookup. Incoming active
guard, bounded extent/address, carrier and separation remain explicit.

`NativeSourcePreservedLengthInside` derives second-source containment
before MCOPY from the incoming native lookup and source bounds, proving
length preservation through the intervening store. Entry guards and native
length provenance remain explicit.

`NativeSourceCopyActiveExtent` proves bounded native MCOPY active-extent
preservation, monotonicity and lookup-guard preservation, including zero-length
copies. Source, destination and length bounds are explicit premises; this does
not admit CREATE2 or establish actual entry geometry.

`NativeSourceFirstCopyActive` connects the actual first-copy state to native
MCOPY active extent, preserving its upper bound and lookup guards under explicit
source, destination and length bounds. Original-entry geometry remains open;
these laws do not admit CREATE2.

`NativeSourcePreludeActive` propagates bounded active extent through the
prelude MLOAD and first MCOPY, with explicit address and length premises.
Decoded-context geometry and CREATE2 admission remain open.

`NativeSourceDecodedCopyActive` propagates bounded active extent through
the free-pointer MLOAD at address 64 and the decoded prelude/copy path.
Operand bounds remain premises; full entry geometry and CREATE2 remain open.

`NativeSourceContextCopyActive` propagates the original active-extent bound
through field loads/stores, allocation, free-pointer and length loads, and the
first MCOPY. Original operand bounds remain explicit; CREATE2 remains closed.

`NativeSourceContextLengthInside` derives second-source containment for the
actual packed context using an active-extent bound propagated from the original
state. Lookup guards, source geometry and entry bounds remain explicit; this
does not establish canonical initcode or admit CREATE2.

`NativeSourceGuardedContextInside` derives the intercopy store address bound
and padding from the actual second allocation guard and an explicit nonwrap
bound. Lookup/source geometry remains explicit; CREATE2 remains closed.

`NativeSourceDerivedSecondReturn` composes second-source containment with
exact original first-payload return. It replaces the opaque containment premise
with explicit lookup and geometry premises; second-payload provenance, canonical
initcode, full entry and CREATE2 admission remain open.

`NativeSourceLoadActiveGuard` proves bounded MLOAD extent monotonicity,
preservation of an existing active guard and establishment of the loaded
address guard. Byte-carrier containment is separate; CREATE2 remains closed.

`NativeSourceSizeActiveGuard` establishes active guards at the native MSTORE
address and the actual sizeword address. Carrier containment and subsequent
guard propagation remain separate obligations; CREATE2 remains closed.

`NativeSourceAllocatorActiveGuard` preserves query guards through the actual
first allocator and propagates the sizeword guard. Later load/copy propagation
and carrier/provenance obligations remain open; CREATE2 remains closed.

`NativeSourcePreludeActiveGuard` preserves an existing active query guard
through the prelude length load and first MCOPY under explicit bounds.
Decoded/context composition and byte provenance remain open; CREATE2 is closed.

`NativeSourceDecodedActiveGuard` preserves existing active guards across
the pointer load and decoded first-copy path. Operand bounds and carrier
containment remain explicit; CREATE2 remains closed.

`NativeSourceContextActiveGuard` derives the actual sizeword active guard
after the first copy from bounded original operands, through field writes,
allocation and loads. Carrier containment and byte provenance remain separate;
CREATE2 remains closed.

`NativeSourceActiveDerivedReturn` derives the intermediate sizeword active
guard in the exact first-payload return theorem. Carrier containment, separation
and source provenance remain premises; CREATE2 remains closed.

`NativeSourceSizewordCarrier` proves all 32 sizeword bytes are contained
after the actual size store and first allocator, under explicit padding and
address premises. Copy propagation and CREATE2 admission remain open.

`NativeSourceCopyCarrierMonotone` proves snapshot-write and actual first-copy
carrier monotonicity, including zero length, under explicit source containment
and padding. Context provenance and CREATE2 admission remain open.

`NativeSourceContextCopyCarrier` transports sizeword containment through
the actual prelude/decoded/context copy, including zero length, using bounded
intermediate lemmas. Padding/source premises and CREATE2 remain open.

`NativeSourceGuardedSizewordCarrier` derives copied sizeword containment
and intermediate padding from original source/address bounds and the actual
second allocation guard. Separation/provenance and CREATE2 remain open.

`NativeSourceCarrierDerivedReturn` derives copied sizeword containment in
the exact first-payload return theorem. Separation and second-source provenance
remain explicit premises; canonical initcode and CREATE2 remain open.

`NativeSourceSizewordSeparation` derives actual free-pointer ordering from
the first allocation guard and separates the sizeword from the intercopy store
under nonwrap. Source provenance and CREATE2 remain open.

`NativeSourceSeparatedReturn` derives sizeword/intercopy-store separation
from actual allocator guards in the exact first-payload return theorem.
Second-source provenance and full CREATE2 admission remain open.

`NativeSourceCopyLookupFrame` preserves exact native lookup below MCOPY
destination, deriving post-copy carrier/active guards, including zero length.
Actual source provenance and CREATE2 remain open.

`NativeSourceFirstCopyLookup` connects actual first-copy memory and native
lookup preservation below its destination. Bounds/guards remain explicit;
full context provenance and CREATE2 remain open.

`NativeSourcePreludeLookup` preserves native lookup through MLOAD and the
actual prelude/firstcopy under explicit bounds and pre-copy guards. Decoded
context provenance and CREATE2 remain open.

`NativeSourceDecodedLookup` preserves exact query lookup through the free
pointer load and decoded first-copy path under explicit bounds and guards.
Actual sizeword provenance and CREATE2 remain open.

`NativeSourceContextLookup` preserves the actual sizeword lookup across the
first copy with derived active guards and explicit carrier/separation premises.
Sizeword contents and full CREATE2 admission remain open.

`NativeSourceGuardedContextLookup` derives intermediate carrier, padding
and separation from original bounds and the actual first allocation guard in
sizeword lookup preservation. Sizeword value and CREATE2 remain open.

`NativeSourceSizewordBytes` establishes exact bytes written by the actual
sizeword MSTORE, retaining the native subtraction/addition expression. Later
allocator preservation, length interpretation and CREATE2 remain open.

`NativeSourceAllocatedSizewordBytes` preserves exact sizeword bytes across
the first allocator and derives native lookup using word roundtrip and actual
carrier/active guards. Full context length and CREATE2 remain open.

`NativeSourceContextSizewordValue` establishes the exact native sizeword
value after actual first-copy execution from original bounds and first guard.
Natural length interpretation, source provenance and CREATE2 remain open.

`NativeSourceSizewordNatural` interprets the native sizeword expression as
finish minus base minus 32 under ordered endpoints, proving its source-end
equality. Actual operand geometry/provenance and CREATE2 remain open.

`NativeSourceSizewordSourceExtent` derives source containment and bounded
length from the exact sizeword and ordered geometric endpoints. Actual endpoint
relations and byte provenance remain obligations; CREATE2 remains closed.

`NativeSourceContextSecondSourceExtent` derives actual second-source
containment from the exact copied sizeword and explicit source/end geometry.
Those endpoint relations and byte provenance remain to prove; CREATE2 is closed.

`NativeSourceGeometricSecondReturn` derives the second-source lookup extent
in exact first-payload return from explicit endpoint geometry. Actual endpoint
relations and second-payload bytes remain obligations; CREATE2 remains closed.

`NativeSourceEntryContainedReturn` derives post-copy endpoint containment
from returned allocator memory using exact copy monotonicity. Endpoint geometry,
second-payload bytes and CREATE2 admission remain open.

`NativeSourceFieldEndpointCarrier` derives returned memory extent from the
actual last field store and bounds any endpoint below c+320. Actual endpoint
relations and second-payload provenance remain open; CREATE2 is closed.

`NativeSourceFieldBoundedReturn` derives the allocator-entry containment
premise for exact first-payload return from the fieldstore extent and explicit
b <= c+320. Endpoint/source geometry and second-payload provenance remain
open; CREATE2 admission remains closed.

The `b <= c+320` specialization is conditional, not a general entry
contract: the pinned source Yul initializes dynamic-array output at
`expr_mpos+352` and advances it by 128 per element. A general endpoint
carrier proof must account for those prior writes; the field bound alone
cannot discharge it.

`NativeSourceDynamicElementCarrier` proves exact native memory extent for
four word stores at offsets 0/32/64/96, matching the array encoder layout.
It is a memory component; native loop execution and its iteration invariant
remain unproved. It does not change CREATE2 admission.

`NativeSourceDynamicLoopDecode` authenticates the five MLOAD and four
MSTORE instructions in the pinned array-encoding loop. Stack/address and
iteration proofs remain open; this does not admit CREATE2.

`NativeSourceDynamicFirstStore` composes the pinned MLOAD/AND/DUP5/MSTORE
at PCs 744..747 under an explicit entry stack and proves its exact native
memory effect. Derivation of that stack from loop entry and the remaining
element stores are still required; CREATE2 remains closed.

`NativeSourceDynamicFirstLoad` composes the seven native instructions at
741..747 from an explicit stack, including the pointer load and the first
masked element store. Loop-entry provenance and the other three stores remain
open; CREATE2 admission is unchanged.

`NativeSourceDynamicSecondStore` proves the eight decoded instructions
at 748..755, loading at a+f and storing at d+f with an exact memory frame.
Loop-entry operands and the other element stores remain obligations; CREATE2
admission is unchanged.

`NativeSourceDynamicTwoStores` composes the first two element stores into
15 decoded native steps at 741..755 with stride32. Its memory frame preserves
the second lookup in the state after the first store, including possible
aliasing. Loop provenance and the remaining stores remain open.

`NativeSourceDynamicThirdStore` proves the eight decoded instructions
at 756..765, including both PUSH1 64 immediates, and the exact native store
from a+64 to d+64. Loop provenance, composition and the final element store
remain obligations; CREATE2 remains closed.

`NativeSourceDynamicFourthStore` proves the seven decoded instructions
at 766..773, including PUSH1 96, and the exact masked store at dest+96.
Composition of all element stores, loop entry and the iteration invariant
remain open; CREATE2 admission is unchanged.

`NativeSourceDynamicElementExecution` composes all four stores into
30 decoded native steps at 741..773, with the exact sequential memory state.
It proves the output stack and endpoint containment dest+128 under explicit
platform/address bounds. Loop entry, increments and induction remain open;
CREATE2 remains closed.

`NativeSourceDynamicIncrements` proves the eight decoded arithmetic and
shuffle instructions at 774..781, the exact resulting stack, and unchanged
memory. The branch back to the header, loop-entry provenance and induction
remain open; CREATE2 admission is unchanged.

`NativeSourceDynamicBackedge` proves raw native PUSH2 551/JUMP at
782..785, memory preservation and the JUMPDEST decode at 551. This raw step
proof does not establish jump-scanner membership or checked-execution gas
conditions; those remain required, along with loop induction.

`NativeSourceDynamicIterationSuffix` composes writes, increments and raw
backedge into 40 decoded steps from 741 to the header at 551, preserving
endpoint containment dest+128. Entry provenance, checked gas/jump conditions
and loop induction remain open; CREATE2 remains closed.

`NativeSourceDynamicEntry` derives the explicit stack and unchanged memory
after 16 decoded setup instructions at 718..740. Decode proofs are separated
in `NativeSourceDynamicEntryDecode` to bound build memory. Provenance from
the header, checked conditions and loop induction remain open.

`NativeSourceDynamicBody` composes setup and the write suffix into
56 decoded native steps from 718 back to 551, deriving the counter+1,
source+32 and destination+128 stack updates and endpoint containment.
The header condition, checked execution and induction remain open.

`NativeSourceDynamicHeader` proves six decoded steps at 551..558,
branching to 718 exactly when unsigned index<count and otherwise to 559.
The input stack is preserved. Exit execution, checked conditions and
loop induction remain open; CREATE2 admission is unchanged.

`NativeSourceDynamicExit` proves 11 decoded exit instructions at 559..572,
ending at573 with exact operand stack and unchanged memory. Endpoint
containment is preserved; deriving it from all loop iterations remains open.
CREATE2 admission is unchanged.

`NativeSourceDynamicIteration` composes the exact unsigned header test
and body into62 raw native steps under index<count, preserving code and
returning to551 with exact register updates and endpoint containment.
Zero-inclusive loop induction and checked conditions remain open.

`NativeSourceDynamicLoopInduction` proves zero-inclusive execution of
62*n native steps and preserves exact advanced registers and endpoint
containment. Its recursive Good premise still requires per-iteration guards
and nonwrapping endpoints; deriving Good from initial geometry, termination
and checked conditions remains open.

`NativeSourceDynamicLoopGeometry` derives all iteration guards from
initial count and endpoint bounds, computes advanced counter/endpoint values
and proves the exit condition after the remaining count. Native execution
no longer assumes recursive Good directly; initial-state provenance, exit
composition and checked conditions remain open.

`NativeSourceDynamicLoopReturn` composes n iterations and the terminating
header/exit into62*n+17 raw native steps to573, including n=0, preserving
final endpoint containment. Initial header provenance/bounds and checked
execution conditions remain explicit obligations; CREATE2 remains closed.

`NativeSourcePrecontainedReturn` preserves memory containment from573
through field stores, sizeword and allocator, replacing the intermediate
endpoint premise in exact first-payload return with entry containment.
Loop-to-entry operand composition and full CREATE2 obligations remain open.

`NativeSourceDynamicMappedEndpoint` connects the actual573 stack to
advanced loop registers, proves its b endpoint is contained, and preserves
source/base relations and ordering from initial geometry. Initial geometry
still requires source-code provenance; CREATE2 remains closed.

`NativeSourceLoopFirstPayload` specializes exact first-payload return to
the native loop-derived573 operands, deriving endpoint containment, source
value and ordering from initial loop geometry. Other bounds/guards and
initial-code provenance remain explicit; CREATE2 remains closed.

`NativeSourceDynamicLengthStore` proves five decoded steps at 535..539,
writing the loaded array length and establishing address+32 memory extent
independently of that length. Its address/base provenance and the remaining
header setup remain open; CREATE2 admission is unchanged.

`NativeSourceDynamicHeaderSetup` proves eight decoded instructions at
540..550, producing index0, count, source+32 and destinationbase+352 at551.
Memory and code are preserved. Composition with the preceding length store
and initial pointer provenance remain open; CREATE2 remains closed.

Native dynamic-array initialization: `NativeSourceDynamicInitialInvariant` composes the actual PC535 length store and PC540 header setup into thirteen raw EVM steps to PC551. It derives the initial loop endpoint containment, including an empty array, from the length-store extent under the explicit target relation `x0 = x7 + 320` and nonwrapping address bounds. Earlier-code provenance, checked gas/jumps, complete initcode and CREATE2 admission remain unproved by this module.

`NativeSourceDynamicInitialReturn.execute` composes PC535 initialization with the counted dynamic loop and exit to PC573 in `13 + (62 * count + 17)` raw steps, where count is the initial array-length MLOAD. It derives the initial invariant instead of assuming it. Initial target/base relation and natural count/endpoint bounds remain hypotheses; earlier source provenance, checked gas/jumps, payload equivalence and CREATE2 admission are still open.

`NativeSourceDynamicTarget` authenticates native PC499–504 (`PUSH2 320; DUP13; ADD; SWAP14`): four raw steps place `x11 + 320` at stack index 14 and preserve memory. Tracking this target to PC535 and deriving the base/source relations remain open, as do checked execution and CREATE2 admission.

`NativeSourceDynamicTargetField` proves the actual five steps PC505–510: MLOAD, PUSH1 64, DUP14, ADD and MSTORE. The stored word comes from the native entry memory, and the buried target register survives at output index 13. Subsequent field stores and complete target/base provenance to PC535 remain open, along with checked execution and CREATE2 admission.

`NativeSourceDynamicTargetMaskedFirst` and `NativeSourceDynamicTargetMaskedSecond` prove the actual masked stores PC511–517 and PC518–524. Each uses its own entry memory lookup, bitwise AND, and the native destination addition (96 or 128); buried target registers survive. Composition must retain the second lookup after the first store. Transport through PC525–534, earlier base/source provenance and checked CREATE2 equivalence remain open.

`NativeSourceDynamicTargetMaskedPair` composes PC511–524 into twelve raw native steps and preserves the buried target at output index 9. Its second lookup explicitly uses the state after the first masked store, with no aliasing assumption. PC525–534 transport, earlier provenance and checked CREATE2 equivalence remain open.

`NativeSourceDynamicTargetSuffix` proves the seven actual instructions PC525–534, including SWAP9 and the store of 256 at base+160. Its exact output stack places the incoming buried target x9 at the head and retains base x7 at index 7. Complete composition with the earlier target calculation and provenance before PC499 remain open; checked CREATE2 equivalence is not established.

`NativeSourceDynamicTargetTransport` composes the actual 28 steps PC499–534. It derives the final head pointer as final base (stack index 7) plus 320, using sequential native memory states throughout. This discharges target transport for this fragment; earlier source/base provenance, integration into full entry execution, checked gas/jumps and CREATE2 equivalence remain open.

`NativeSourceDynamicTransportReturn` composes native PC499 transport, initialization and counted loop exit to PC573. The target/base relation is derived from instructions, with six explicit tail words completing the initial register map. The count is loaded through the actual post-field-store array pointer. Count and endpoint bounds, source provenance before PC499, checked gas/jumps and complete CREATE2 equivalence remain open.

`NativeSourceDynamicSourceSetup` proves the actual eight steps PC489–498. The output at PC499 has stack index 9 equal to base (index 11) plus 32; the native store writes 32 at that address. Composition with target transport and loop return, earlier provenance and checked payload/CREATE2 equivalence remain open.

`NativeSourceDynamicSourceReturn` composes PC489 source setup, target transport, initialization and the counted loop to PC573. It derives the initial loop register relation source=base+32 and base+32≤destination under explicit nonwrap bounds. Actual post-field-store memory supplies the length. Earlier entry provenance, bound derivation, full payloads and checked CREATE2 equivalence remain open.

`NativeSourceDynamicSourceInvariant` derives the exact source-prepared initial loop invariant, remaining-count equality, terminal PC573 and endpoint containment from native PC489 setup/transport under explicit initial count/address bounds. It includes zero length. Earlier calldata provenance, derivation of bounds, payload equality and checked CREATE2 equivalence remain open.

`NativeSourcePreparedFirstPayload.readback` specializes exact first-payload byte equality to the PC489-prepared loop operands. It derives the initial invariant, remaining count, endpoint geometry and source/base/order relations; allocation/copy bounds and guards remain hypotheses. Original calldata provenance, second payload, canonical initcode and checked CREATE2 equivalence remain open.

`NativeSourceSecondPayloadSized` preserves exact second-payload bytes through the real MSTORE at PC667 and sizing steps. Its frame includes the store, with an explicit natural end-address relation and source/copy containment premises. Later size-word/allocation transport, actual source provenance, canonical initcode and checked CREATE2 equivalence remain open.

`NativeSourceSecondPayloadGeometry` derives copy endpoint containment from native memory-write growth and the MSTORE667 end-address relation from initial nonwrapping addition bounds. Its exact second-payload readback no longer assumes those intermediate facts. Source preservation, positive-length handling, later allocations and checked CREATE2 equivalence remain open.

`NativeSourceSecondPayloadAllocated.readback` preserves exact second-payload bytes through MSTORE667, size-word MSTORE675 and allocator return. It derives intermediate containment and finish geometry from native copy plus nonwrapping bounds. Source preservation, positive amount and separation from size/allocator stores remain explicit; actual context provenance and checked CREATE2 equivalence remain open.

`NativeSourceSecondPayloadOriginalTotal.readback` covers empty and nonempty second payloads against a distinct original byte array through allocator return. It derives loaded-source preservation from entry-memory preservation and separation from the intercopy store. Actual source provenance, initial bounds and checked CREATE2 equivalence remain open.

`NativeSourceFirstCopySourceWindow` proves that the actual first MCOPY preserves a source window below its destination, including zero-length copies and reads. It retains native snapshot semantics and explicit source containment/padding/separation bounds. Actual context provenance and complete CREATE2 equivalence remain open.

`NativeSourceTwoCopySecondPayload.readback` composes the first-copy source frame with total second-payload readback through allocator return, referencing memory before the first copy. It derives intermediate source equality and containment, including zero lengths. Actual context operand mapping, initial bounds/separation and checked CREATE2 equivalence remain open.

`NativeSourceContextSecondPayloadBytes` instantiates total second-payload byte preservation with actual context length/free pointer/amount and both copy states, referencing PC632 entry memory. A generic decoded-memory frame avoids expanding nested allocations in kernel reduction. Initial bounds/separation, canonical ABI provenance and checked CREATE2 equivalence remain open.

`NativeSourceFieldWriteSnapshots` records exact memory updates for the four native ABI field stores and the length-word store. These retain `mstore` and its padding semantics; they do not assume the encoded source is unchanged. Canonical field-value composition and checked CREATE2 admission remain open.

`NativeSourceContextFieldWrites` instantiates the four field memory updates at actual context operands. Values use sequential native lookups (and address masks), and writes use exact byte-array word encoding. Source aliases are not assumed absent. Length-word and allocator composition, canonical ABI provenance and checked CREATE2 equivalence remain open.

`NativeSourceContextSizedBytes` composes the four sequential field encodings and actual length-word write into an exact memory expression before the first allocator. A scalar size-word lemma bounds kernel reduction. The expression retains modular length arithmetic and native lookups; canonical ABI interpretation, allocator transport and checked CREATE2 equivalence remain open.

`NativeSourceContextAllocatedBytes` proves the exact allocator memory update at word 64 and composes it with actual context field and length-word encodings at PC632. It preserves sequential native lookups and modular arithmetic without disjointness assumptions. Canonical ABI interpretation, operand bounds and checked CREATE2 equivalence remain open.

`NativeSourceLengthwordGeometry` derives the natural length `finish-base-32` from the exact modular length word when `base+32 <= finish`, and proves the second-source endpoint under the source relation. Generic modular arithmetic lemmas bound kernel reduction. Actual context lookup transport and canonical ABI provenance remain open.

`NativeSourceSecondAmountGeometry` derives the natural second-copy amount from the actual intercopy lookup using existing lookup preservation. Carrier bounds, separation, active-word guards and the input length-word equality remain explicit; it does not infer canonical source provenance or checked CREATE2 equivalence.

`NativeSourceContextSecondAmount` derives the actual second-copy natural length and endpoint using native length-word lookup provenance through field writes, allocator and first copy. The word-value hypothesis is discharged; carrier, active-word guards, separation and source/order relations remain explicit. Canonical input provenance and checked CREATE2 equivalence remain open.

`NativeSourceContextSecondAmountGuards` derives both active-word lookup guards and the length-word value in the actual second-copy context. It reuses bounded first-copy and intercopy-store extent laws. Scalar bounds, carrier/separation/order and allocator guards remain explicit; canonical input provenance and checked CREATE2 equivalence remain open.

`NativeSourceContextSizewordCarrier` derives length-word containment through its store, allocator and first copy. Its natural-length theorem also derives padding from scalar address bounds and both active-word guards. First-copy source containment, input/address bounds, separation/order and allocator guard remain explicit; canonical input provenance and checked CREATE2 equivalence remain open.

`NativeSourceContextSecondAmountContained` derives first-source containment at PC632 from original memory containment through the actual fields and allocator. The second-amount natural-length result no longer assumes this intermediate containment. Original source bounds, separation/order and allocator guard remain explicit; canonical input provenance and checked CREATE2 equivalence remain open.

`NativeSourcePreparedSecondGeometry` derives the final second-source/base relation, source/end order and endpoint containment for the actual PC489-prepared loop registers, including zero iterations. Initial scalar endpoint/count bounds remain explicit; earlier calldata provenance and checked CREATE2 equivalence remain open.

`NativeSourcePreparedSecondLength` proves the actual prepared-loop output stack (including the repeated base register), endpoint, modular length word and actual second-copy amount `320 + 128*n`. Order is derived from the native loop; scalar input bounds, separation and allocator guards remain explicit. Canonical input provenance and checked CREATE2 equivalence remain open.

`NativeSourceContextEncodedReadback` identifies final second-payload bytes with an extract of the explicit sequential field, length-word and allocator-pointer writes, rather than an opaque PC632 memory state. Native lookup order and masks are retained. Copy bounds/separation and correspondence to canonical calldata ABI values remain open; no CREATE2 admission follows yet.

`NativeSourceContextSourceExtract` proves allocator preservation of source extracts above 96, including empty extracts, and identifies final second-payload bytes with the preallocator field/length encoding. Postallocator source containment is derived from the sized carrier. Copy bounds/separation and canonical input provenance remain explicit/open; CREATE2 remains closed.

`NativeSourceContextFieldSourceExtract` removes the length-word and allocator-pointer writes from final second-payload readback using total extract frames, including empty lengths. The result references post-fourfield memory, preserving intentional field modifications. Word/source separation, copy bounds and canonical input provenance remain explicit/open; CREATE2 remains closed.

`NativeSourcePreparedSourceWindow` derives the exact end and containment of the actual second-source window of `320 + 128*n` bytes through the four field writes, plus separation from the adjacent length word. Field-write monotonicity uses bounded padding. Initial scalar bounds and canonical input provenance/checked CREATE2 equivalence remain open.

`NativeSourcePreparedSecondPayload` instantiates final second-payload readback on the actual PC489-prepared loop result. It derives the amount, source containment, adjacent-word separation and padding from the certified loop and context laws. Allocation/copy separation guards and canonical initial ABI provenance remain explicit/open; CREATE2 remains closed.

`NativeSourceDynamicElementBytes` exposes the four exact byte writes for a native dynamic collateral element: masked token, two scalar words, masked oracle. Every lookup retains its actual sequential machine state, including the initial load state; no non-aliasing or original calldata provenance is assumed. Canonical whole-array encoding and checked CREATE2 admission remain open.

`NativeSourceDynamicElementSourceFrame.read_below` proves that the actual four sequential collateral-element stores preserve every positive bounded source window contained in the entry memory and ending before the destination. A single destination bound supplies all store offsets and padding bounds; successive source containment follows from memory growth. This byte frame does not establish lookup active-word guards, original calldata provenance or canonical whole-array encoding.

`NativeSourceDynamicLoopSourceFrame` proves preservation of a source byte window through the native body, arbitrary counted iterations and loop exit (including zero iterations). The counted theorem derives iteration bounds from count/endpoint bounds and the existing loop invariant. Original source separation before the initial destination remains explicit; decoder provenance and active-word lookup guards still need proof. This does not admit CREATE2.

`NativeSourceMarketCalldata` defines the explicit canonical word layout for `SourceCaller.deploy(Market,uint256,uint256)` and proves aligned loads from the original byte calldata for all eight Market head fields, the collateral count, and every indexed four-word collateral element. Values retain modulo-256-bit semantics; canonical address/range checks are not assumed proved. These input lemmas do not certify native ABI decoder memory provenance, arbitrary noncanonical offsets or invalid-input rejection equivalence.

`NativeSourceAddressDecoderLoad` certifies the pinned opcode at PC945 and derives its original aligned calldata value and exact stack/world/memory/PC frame from successful checked execution. Unlike the raw counted-loop execution lemmas, this load uses the checked-step path. It does not prove success, address canonicality, the full native decoder, or invalid-input rejection equivalence.

`NativeSourceAddressCanonicality` proves the actual shift/subtract mask is `2^160-1`, masking computes reduction modulo `2^160`, and the original-minus-masked guard vanishes exactly for a 160-bit address. These are arithmetic facts over native UInt256, including the noncanonical direction. The helper instruction sequence and checked branch/revert behavior remain to be connected.

`NativeSourceAddressGuardExecution` proves the pinned ten-instruction sequence PC946..958 executes to the original-minus-masked guard, with unchanged memory, and that its actual stack head is zero exactly for a 160-bit word. Fixed immediates and individual decodes are kernel checked. This uses raw native steps; checked branch/return/revert and complete decoder provenance remain open.

`NativeSourceAddressBranch` certifies the pinned PUSH2/JUMPI at PC959/962, derives destination963 exactly for canonical 160-bit words and91 otherwise, and proves the native JUMP return at963. Branch stack/memory frames are exact. These raw-step facts do not prove scanner/gas checks or final revert behavior at91; CREATE2 remains closed.

`NativeSourceAddressHelper` composes the actual guard and branch from PC946: thirteen raw native steps return the original canonical word to the supplied return PC with world/memory unchanged; twelve steps reach PC91 for noncanonical words. Bounded code/world/return frame lemmas avoid reducing the full nested state in the kernel. Original calldata load composition, checked scanner/gas conditions and final rejection behavior remain open.

`NativeSourceAddressInputReturn` connects the native address helper to its actual calldata load at945: fourteen raw steps return the loaded word for a canonical address; thirteen reach rejection PC91 otherwise. Aligned output values are proved against the original byte calldata. The final revert at91 and checked gas/scanner behavior remain open; these are not whole-decoder acceptance/rejection proofs.

`NativeSourceEmptyRevert` certifies rejection-block decodes91..94 and its raw three-step preparation of `REVERT(0,0)`. It proves the exact empty output and an `EVM.X` revert for the final instruction under its successful native `Z` precheck, including the remaining gas. The checked prefix and helper-to-revert composition remain open; exceptional gas failures are not classified as Solidity reverts.

`NativeSourceRejectionChecks` derives native `Z` acceptance for PUSH0/DUP1 from explicit gas and stack bounds, and for REVERT(0,0) from its stack shape/depth alone. The latter has zero memory-expansion and instruction cost. These facts do not yet compose the complete path or derive its total gas budget.

`NativeSourceCheckedRejection.execute_exact` proves the entire pinned rejection block in native `EVM.X`: from PC91, at least six gas and at most1022 stack words, it returns an empty revert with exactly the initial gas minus six. Every local `Z` precheck follows from those initial bounds; no accepted-check premise remains. The full checked address helper and decoder memory provenance remain open.

`NativeJumpScannerFrame.preserves` proves that native `D_J_aux` retains every previously discovered destination for arbitrary suffix fuel, code and scanner position. This supports bounded prefix certificates without reducing the whole pinned bytecode scanner. It does not yet establish membership of PC91 or any return destination; checked helper execution and CREATE2 admission remain open.

`NativeSourceJumpDestinations` certifies 63 exact native scanner transitions from PC0 through PC91, skipping PUSH immediate bytes. Their composition reaches PC92 with destinations18/50/91 accumulated; suffix preservation proves PC91 belongs to the full native `D_J` result. All proofs are bounded; this does not establish gas/stack checks for the address helper or admit CREATE2.

`NativeSourceJumpChecks` bridges native UInt256 membership to the actual Boolean scanner lookup, proves `notIn=false` for rejection PC91, and derives native `Z` acceptance for JUMPI from explicit ten-gas and stack bounds. Its PC91 specialization uses the proved pinned scanner membership, with no assumed check success. Full checked helper execution/gas composition remains open; CREATE2 admission is unchanged.

`NativeSourceCheckedJumpRejection.execute_exact` composes the native checked JUMPI at PC962 with the complete rejection block: for pinned code, stack91/nonzero-condition/tail, tail length≤1022 and gas≥16, actual `EVM.X` returns empty revert with initial gas minus16. Scanner validity and every local precheck are derived. Earlier address-helper instructions and their total gas remain open; CREATE2 stays closed.

`NativeSourceCheckedPushRejection.execute_exact` extends the checked rejection path to PC959: native PUSH2 costs3, followed by JUMPI10 and rejection6. Given a nonzero condition and explicit stack/gas bounds, actual `EVM.X` returns an empty revert with exactly initial gas minus19. No shared arbitrary instruction cost is used for this composition. Earlier guard/load checks remain open.

`NativeSourceGuardChecks` derives actual native `Z` acceptance at cost3 for SWAP1, PUSH1, SHL, SUB, DUP3 and AND, with explicit opcode-specific underflow/overflow bounds. These local facts cover all instruction types of PC946..958; composing the ten-step checked trace and its total gas is still required.

`NativeSourceCheckedGuard` composes all ten native checked instructions PC946..958 with a derived 30-gas chain. Its `reject_exact` proves actual `EVM.X` rejects a noncanonical address word with empty bytes and exactly initial gas minus49, including scanner-valid branch and rejection block. Explicit initial gas≥49 and tail≤1019 ensure every local check; original PC945 load and canonical return still require checked composition.

`NativeSourceCheckedInputRejection.reject_exact` starts at the real CALLDATALOAD PC945 and proves actual native `EVM.X` rejection when that original calldata word is not a canonical 160-bit address. With explicit gas≥52 and stack headroom, result is empty revert with exactly initial gas minus52. All load/guard/branch/rejection checks are derived; the canonical checked return and full decoder provenance remain open.

`NativeSourceCheckedReturn` proves native checked zero-condition JUMPI and checked JUMP return. `execute_branch_return` composes PUSH2/JUMPI/JUMP from PC959 with gas≥21 and explicit return-destination membership in the actual scanner. This is a continuation equivalence, not a whole-call success claim. Full canonical helper composition and pinned return membership certificates remain open.

`NativeSourceCheckedCanonical` composes the complete canonical helper from the actual PC945 calldata load to its return continuation. It returns the original word at the supplied return PC and proves exactly54 gas consumed, assuming explicit scanner membership for that PC and initial gas/stack bounds. World/memory frame composition and pinned destination memberships remain open; resource-heavy frame attempts are retained as failed evidence.

`NativeSourceCanonicalFrames` proves world-state and memory preservation for the full checked canonical address helper result through bounded return/fallthrough/push/load projection lemmas. This discharges the frame obligations left by the resource-stopped monolithic reduction; earlier failed receipts remain preserved. Pinned return-destination scanner certificates and complete ABI decoder provenance remain open.

`NativeSourceReturnScannerFirst` proves native scanner membership of the actual address-helper return PCs191 and210 by extending the certified prefix with72 exact transitions through PC210, respecting PUSH immediate lengths. The remaining pinned return PCs381/395/862/894 still require certificates.

The checked address-helper results above start at PC945 (CALLDATALOAD). The six actual pinned caller sites jump to PC944 (JUMPDEST), then execute PC945; covering that entry requires an additional checked step and one gas unit. Static disassembly confirms return PCs191/210/381/395/862/894, but is not a substitute for native scanner membership or execution proofs. The PC944 composition is staged and remains unverified.

The bounded scanner continuation is now compiled and audited through PC559 (`NativeSourceReturnScannerPart1`–`Part4`). These local transition certificates do not by themselves establish all selected return memberships: the remaining blocks and final prefix/suffix composition are still being validated. The generic `NativeJumpScannerStep.step` avoids reducing the concrete runtime inside the scanner rule.

The remaining address-helper scanner certificates are complete: all nine bounded blocks and the composed native scanner prove membership of PCs191/210/381/395/862/894. `NativeSourceAddressEntry` covers the actual PC944 JUMPDEST entry with checked canonical continuation (55gas) and noncanonical empty revert (53gas), under explicit initial gas/stack and return-membership conditions. `NativeSourceMarketAddressCalls` instantiates original canonical ABI midnight/loanToken/enterGate/liquidatorGate words and their PC945 helper calls. These are focused native proofs, not full ABI memory-decoder provenance or CREATE2 admission; both remain open.

`NativeSourceAddressEntryCertificate` makes the actual PC944 canonical helper usable at the six pinned return sites without a remaining scanner-membership assumption: membership is derived from `NativeSourceReturnMembership`. Bounded returned-stack/world/memory laws relate its result directly to the original input state. Full decoder allocation and field-store provenance remain open.

`NativeSourceMidnightFieldStore` certifies exact decodes and native transitions PC191..198, with preparatory costs1/3/3/3/3/3 and explicit final MSTORE cost. The final memory is exactly native mstore(base+32, word), with the actual remaining stack and unchanged world state. These are native step facts: deriving MSTORE memory-expansion checks and composing the checked segment with original calldata remain open.

`NativeSourceFieldStoreChecks` derives native DUP4/DUP2/ADD prechecks and actual MSTORE `Z` acceptance from gas≥computed memory expansion+3 and stack bounds. Its PC198 continuation charges the real expansion before the native store step. No zero-expansion or successful-check premise is assumed. Prefix composition and original calldata-to-memory readback remain open.

`NativeSourceCheckedFieldPrefix` composes the six checked native instructions PC191→198 and the following MSTORE. The prefix consumes exactly 16 gas; the full segment requires 19 plus the actual native memory-expansion cost at PC198. Stack headroom and gas bounds derive all prechecks, with no assumed successful check or zero expansion. Original calldata/helper-to-memory composition and full decoder equivalence remain open.

`NativeSourceMidnightDecodedStore` composes the actual PC944 canonical address helper (return destination191 derived from the pinned scanner) with PC191..198 and native MSTORE. Original canonical ABI calldata determines the stored `Market.midnight` word; byte readback is proved under an explicit platform-padding bound, and remaining gas is exactly initial gas minus74 minus computed native expansion. Dispatcher/allocation provenance, derivation of the padding bound, active-memory lookup guards and the remaining decoder fields are still open. This does not admit CREATE2.

`NativeSourceLoanCallSetup` certifies the six actual instructions PC199..209, preparing the `loanToken` address-helper call at PC944 with return PC210. Its checked composition consumes exactly23 gas and preserves world/memory; stack and calldata offset derive from the real DUP4/ADD sequence. Scanner membership of944 remains explicit in this module. The subsequent helper/store and full dispatcher provenance remain open.

`NativeSourceHelperScanner` extends the pinned native scanner by35 exact instruction transitions PC895→945 and proves PC944 membership in the real `D_J` result. It uses generic scanner-step lemmas and concrete byte/parse certificates; no static-byte-only substitute for scanner membership. Full decoder execution and CREATE2 admission remain open.

`NativeSourceLoanCallCertificate` removes the explicit jump-membership premise from PC199 setup and composes it through the real944helper to return PC210. It derives the exact78gas charge and original calldata word/stack/world/memory frames. Canonical Market calldata instantiates the loanToken load at164 when the carried ABI base is96. Proving that base from the dispatcher, the following field store and full ABI equivalence remain open.

`NativeSourceLoanFieldStore` certifies the eight actual instructions PC210..218, including native DUP5/SWAP2 checks and MSTORE atbase+64. Seven checked prefix continuations consume19gas; composing the store requires22 plus actual native memory expansion. Gas and stack bounds derive every precheck. Composition with the preceding loanToken helper, original calldata byte readback and full decoder provenance remain open.

`NativeSourceLoanDecodedStore` composes PC199 setup, the actual944address helper and PC210..218 store. Canonical original Market calldata determines the loanToken bytes stored atbase+64 (carried ABIbase96); byte readback retains the platform-padding bound. Exact remaining gas is initial minus100 minus computed expansion, finalPC219 and stack/world frames are proved through bounded abstract-state lemmas. Dispatcher/allocator provenance, deriving padding/active-memory bounds and full ABI/CREATE2 equivalence remain open.

`NativeSourceAddressPair` composes checked PC944 through both original address-field stores to219. Exact gas is174 plus the two actual expansion charges. A native store-frame lemma preserves midnight bytes across the loanToken write; canonical Market calldata yields both final byte readbacks. The frame retains an explicit allocated-memory bound and address nonwrap, and first readback retains platform padding. These bounds and the carried ABIbase96 still require dispatcher/allocator provenance; full decoder and CREATE2 admission remain open.

`NativeSourceGrowingMemoryFrame` extends byte preservation to native stores that grow memory. It derives the readable midnight span from the first store, then proves the loanToken store starts no later than that memory end, so its platform-padding gap is zero. Both final canonical Market field readbacks therefore require no second-write-in-bounds assumption. Only initial platform padding and address nonwrap remain explicit here, along with the carried ABIbase96; deriving those from the dispatcher/allocator and full decoder/CREATE2 equivalence remain open.

`NativeSourceCollateralOffsetLoad` certifies the four actual instructions PC219..223: PUSH100/DUP4/ADD/CALLDATALOAD. Their checked composition costs12gas, preserves world/memory and loads the original calldata word at carriedABIbase+100. Canonical Market calldata with ABIbase96 produces relativeoffset256. Subsequent offset/calldata-size guards, array allocation/copying, deriving the carried base and full decoder/CREATE2 equivalence remain open.

`NativeSourceCollateralOffsetGuard` records exact decodes PC224/233/234/235/238, the four native preparation transitions (PUSH8 limit, DUP2, GT, PUSH2 rejection destination), and proofs that the computed flag is zero exactly on the accepted side of the64bit bound. These are native step/flag facts; deriving the checked prefix and composing actual accepted/rejection JUMPI paths remains open. Full array decoding and CREATE2 admission remain open.

`NativeSourceCheckedOffsetGuard` derives PUSH8/GT prechecks and composes the four actual guard preparation instructions with JUMPI238. Offsets≤2^64−1 continue atPC239 with original offset/world/memory and exactly22gas consumed; larger offsets execute the real empty-revert block91 and consume28gas. Every local check follows from explicit gas/stack bounds, with destination91 derived from the native scanner. Original offset-load composition and subsequent calldata/array bounds remain open; CREATE2 remains closed.

`NativeSourceOffsetCertificate` composes the original calldata offset load atPC219 with the checked64bit guard. Accepted offsets continue at239 after34gas, preserving world/memory and the original offset on stack; offsets above2^64−1 execute an empty revert after40gas. Canonical Market calldata yields offset256 with carriedABIbase96. The subsequent calldata-size checks, dynamic array decoder and deriving the carried base remain open; CREATE2 remains closed.


`NativeSourceCollateralSpan` certifies the exact eleven decodes at PC239..252 and ten native preparation transitions before JUMPI252. The resulting stack retains the exact signed SLT/ISZERO flag computed from modular offset addition and original calldata size; frame and PC252 results and cumulative gas29 are proved. These are raw native transitions, not yet a checked X composition or a canonical acceptance certificate. Checked preconditions, both JUMPI paths, canonical size/nonwrap bounds, subsequent array decoding and CREATE2 admission remain open.


`NativeSourceSpanChecks` derives generic native Z prechecks for CALLDATASIZE (cost2), SLT and ISZERO (cost3), from explicit gas and stack bounds. This adds no canonical acceptance assumption; checked composition of the collateral span and JUMPI paths remains open.


`NativeSourceCheckedSpan` derives ten checked continuations from PC239 to PC252 and composes them with cumulative gas29. Every precheck follows from explicit gas and stack headroom; the exact signed SLT/ISZERO flag and modular addition are retained. Both JUMPI252 paths and canonical size/nonwrap bounds remain open, as do full array decoding and CREATE2 admission.


`NativeSourceSpanBranches` composes JUMPI252 with the checked span: a zero signed-bound flag continues after39gas; a nonzero flag executes the actual empty-revert block after45gas. These intermediate certificates retain the exact flag as an explicit hypothesis. Deriving its value from original canonical calldata size and nonwrap bounds remains open; CREATE2 admission remains closed.


`NativeSourceSpanBounds` proves signed less-than agrees with the required positive comparison when both operands are below2^255. It derives flagzero at canonicalbase96/offset256 from calldata size at least388 and below2^255. These explicit size bounds still require provenance from the original Market encoding; this is not full decoder or CREATE2 certification.


`NativeSourceMarketSpan` derives original Market calldata size388+128n, proves the actual signed span flag zero and composes checked acceptance toPC253 with39gas under the explicit signed-size bound. The accepted state preserves world and memory. ABIbase96 remains carried; deriving it from the dispatcher, subsequent array decoding and CREATE2 admission remain open.


`NativeSourceCollateralLengthLoad` certifies actualPC253..257 PUSH4/DUP3/ADD/CALLDATALOAD with four checked continuations, cumulativegas12 and world/memory frames. At carried arrayoffset352, original Market calldata yields the actual collateral length word at356 modulo2^256. Subsequent length guards, allocation and loops, and dispatcher provenance remain open; CREATE2 remains closed.


`NativeSourceCollateralLengthGuard` records exact decodes258..272, four native preparation transitions and the64bit length flag characterization. Its destination is786, whose pinned bytecode constructs Panic(0x41), not emptyrevert91. Checked prefix/JUMPI composition and exact panic execution including memory expansion remain open; CREATE2 remains closed.


`NativeSourceCheckedLengthGuard` derives PUSH8/GT prechecks and four checked native continuations from258 to272, with cumulativegas12 and the exact prefix frame. Actual JUMPI272 and Panic(0x41) rejection composition remain open; no rejection payload or zero memory expansion is assumed.


`NativeSourceLengthAccept` proves destination786 belongs to the actual native scanner, derives the checked zero JUMPI272 and composes length-guard acceptance to273 with exact22gas and world/memory frames. Natural lengths≤2^64−1 satisfy the guard after UInt256 conversion. Original calldata-load composition and the exact Panic(0x41) rejection remain open, as do allocation/array decoding and CREATE2 admission.


`NativeSourceLengthCertificate` composes original calldata length loading at253 with the checked64bit guard, reaching273 after34gas and preserving world/memory. Canonical Market calldata at carriedarrayoffset352 supplies its original collateral length, under an explicit64bit length bound. The exact panic rejection, allocation/array loop and deriving carried offsets from the dispatcher remain open; CREATE2 remains closed.


`NativeSourceArrayAllocationDecodes` certifies twelve actual decodes273..291 and five immediates for the allocation call, including return292 and allocator910. These decode certificates alone do not establish execution, MLOAD expansion costs or checked allocator equivalence; full array decoding and CREATE2 admission remain open.


`NativeSourceArrayFreePointer` provides actual native PUSH64/MLOAD/SWAP3 transitions and the free-pointer load frame. `NativeSourceArrayLoadCheck` derives the MLOAD Zcheck and continuation at275 from gas at least the actual memory expansion charge plus3. No zero-expansion assumption or fabricated free pointer is used; full call setup, checked allocator/array decoding and CREATE2 remain open.


`NativeSourceArrayCallOperands` certifies eight raw native transitions277..288: return292, size constant32, DUP4, shift5/SHL, modular ADD, DUP6 and allocator910. They preserve native operand order and modular arithmetic. Full checked call composition, final JUMP/scanner910 and allocator semantics remain open; CREATE2 remains closed.


`NativeSourceArrayOperandChecks` adds SWAP3/DUP6 Zprechecks and eight checked continuations277..288, reusing existing SHL/PUSH/ADD/DUP4 checks. Each follows from explicit stack and gas bounds; full call composition with MLOAD expansion and finalJUMP291 remains open, as does checked allocator/array equivalence.


`NativeSourceArrayCheckedPointer` derives checked PUSH64 at273 and SWAP3 at276, and composes PUSH64/MLOAD with exact gas6 plus the real expansion charge. It retains explicit local gas and stack bounds. Full allocation-call composition, finalJUMP and checked allocator/array equivalence remain open.


`NativeSourceArrayAllocatorJump` derives allocator910 membership from actual native scanner steps and certifies JUMP291 to910, consuming8gas and preserving world/memory. No static-byte-only destination assumption is used. Full allocation-call composition and checked allocator/array equivalence remain open; CREATE2 remains closed.


`NativeSourceArrayCallPrefix` composes eight checked operand instructions277..288 on their exact intermediate states, reaching291 with cumulativegas24. It derives each local budget from one prefix gas bound. Linking this prefix to the original free-pointer load and final allocator jump remains open; CREATE2 remains closed.


`NativeSourceArrayCallJump` composes the eight checked operand instructions with actual JUMP291 to allocator910, consuming32gas and preserving world/memory. Its final stack contains the original pointer, modular size32+(n<<5), return292 and decoder context. Linking original273freepointer loading and checked allocator return remains open; CREATE2 remains closed.


`NativeSourceArrayReadEntry` composes the complete twelve-instruction call273..291 to allocator910, using the original lookupMemory64 pointer. A single gas bound41+actual MLOAD expansion derives all local budgets; exact remaining gas and prepared world/memory frames are proved. Checked allocator execution/return292 and full array decoder provenance remain open; CREATE2 remains closed.


`NativeSourceCheckedAllocatorStart` derives the JUMPDEST precheck and composes checked910JUMPDEST/911SWAP1/912PUSH31 using their actual costs1/3/3, consuming7gas. It does not reuse the earlier homogeneous-cost raw execution as a checked certificate. Remaining rounding/overflow/store/return instructions and full decoder equivalence remain open.


`NativeSourceCheckedAllocatorRounding` derives the NOT precheck and composes actual914DUP1/915NOT/916SWAP2/917ADD/918AND with15gas. The native modular expression(size+word)&~word is retained. Deriving the overflow condition and checked store/return path remains open, together with full decoder/CREATE2 equivalence.


`NativeSourceCheckedAllocatorEntry` composes the actual eight checked allocator instructions910..918 to919, consuming22gas with exact modular rounding and world/memory frames. Overflow checks, free-pointer store and checked return remain open; full decoder/CREATE2 equivalence is not established.


`NativeSourceCheckedAllocatorPointer` derives the LT precheck and composes the five checked instructions919..923 with15gas, computing the modular next pointer and exact overflow flag. It assumes neither nonwrap nor guard success. Remaining limit/branch/store/return checks and full decoder equivalence remain open.


`NativeSourceCheckedAllocatorLimit` derives the OR precheck and checked PUSH8 at924 plus DUP3/GT/OR at933..935. The resulting flag retains both overflow and64bit pointer-limit tests. Their full prefix/branch composition, store/return and full decoder equivalence remain open.


`NativeSourceCheckedLimitPrefix` composes the actual four checked limit instructions924..935 to936 with12gas. The combined native limit/overflow flag is preserved. The branch at939, free-pointer write and checked allocator return remain open.


`NativeSourceCheckedAllocatorBranch` composes checked PUSH2 at936 and JUMPI939 with their actual costs3+10. Scanner-backed destination786 and fallthrough940 are proved for the exact native condition; successful allocation is not assumed. Exact Panic(0x41), free-pointer store and return remain open.


`NativeSourceCheckedAllocatorStore` checks PUSH1 at940 and MSTORE at942, reusing the generic MSTORE precheck and charging actual memory expansion plus3gas. The store writes the supplied pointer at64; the source of that pointer, full allocator composition, return and exact panic rejection remain separate obligations.


`NativeSourceCheckedAllocatorReturn` proves actual scanner membership for292 and the checked JUMP at943, charging8gas and preserving memory/world. Its input stack must carry292; whole allocator composition, pointer bounds and exact panic rejection remain open.


`NativeSourceCheckedAllocatorExit` composes PUSH1 at940, MSTORE942 and JUMP943 to292 under one budget of14 plus actual MSTORE expansion. It derives intermediate gas budgets and exact final gas without assuming zero expansion. The incoming pointer and return stack remain explicit; whole allocator composition and exact panic rejection remain open.


`NativeSourceCheckedAllocatorDecision` composes the six checked instructions924..939 under one25gas budget. The condition remains the native OR of pointer-limit and overflow flags, with exact destinations786/940 and no assumed guard success. Pointer construction, successful-path composition and exact panic rejection remain open.


`NativeSourceCheckedAllocatorPointerDecision` composes the eleven checked instructions919..939 under one40gas budget, preserving modular pointer addition, the exact overflow/limit condition and destinations786/940. It assumes neither nonwrap nor successful allocation. The rounded entry, successful exit and exact panic rejection remain to compose.


`NativeSourceCheckedAllocatorFullDecision` composes all19 checked instructions910..939 with62gas, exact modular rounding and overflow/limit decision, destinations786/940 and memory/world preservation. Frame proofs use intermediate certificates to avoid deep reduction. Successful exit, actual acceptance bounds and exact panic rejection remain open.


`NativeSourceCheckedAllocatorSuccess` composes the22 checked instructions910..943 through return292 under one76gas plus actual MSTORE expansion budget. Acceptance is an explicit native-flag premise; this conditional theorem does not establish actual decoder acceptance. Deriving the premise from original free-pointer/allocation bounds and proving exact panic rejection remain open.


`NativeSourceCheckedAllocatorBounds` derives the native acceptance flag from the natural bound base+roundedAmount≤2^64−1, proving nonwrapping addition and the two zero comparisons. The bound must still be established from the actual decoder state; no unconditional acceptance or panic equivalence is claimed.


`NativeSourceCheckedAllocatorCertificate` derives the native acceptance flag from the natural64bit allocation bound and invokes the complete22instruction checked allocator; it also proves the exact natural pointer value. The original decoder must establish that bound and the gas budget. Exact panic rejection remains open.


`NativeSourceCheckedArrayAllocation` composes the original34 checked instructions from273 through allocator910 and return292, using the original memory lookup at64 and original length-derived size. It derives local gas budgets from117 plus actual MLOAD and MSTORE expansions and proves exact final gas. The natural allocation bound remains explicit; exact panic rejection and array decoding remain open.


`NativeSourceCheckedArrayAllocationFrame` proves return PC292, the exact remaining stack and global-state preservation for both the allocator and original call. Its exit certificate identifies memory exactly as MSTORE64 of the supplied new pointer. Original-state memory composition, allocation bounds, array-loop decoding and exact panic rejection remain open.


`NativeSourceCheckedArrayMemory` composes exact memory equality from the original state through the allocator and original call: final memory equals MSTORE64 of the computed new pointer. A generic MSTORE memory congruence avoids deep reduction; it does not claim active-word bounds, allocation acceptance or array-loop correctness.


`NativeSourceArrayLengthStoreDecodes` certifies the pinned instructions292 JUMPDEST,293 DUP2,294 DUP5 and295 MSTORE. These decode facts do not yet certify length-store execution, memory expansion or array-loop behavior.


`NativeSourceArrayLengthStoreSteps` derives the DUP5 precheck and checked continuations for292 JUMPDEST,293 DUP2,294 DUP5 and295 MSTORE. MSTORE charges actual expansion and writes the supplied length at the supplied pointer. Full prefix composition, original-state bounds, loop and panic rejection remain open.


`NativeSourceArrayLengthStorePrefix` composes the four checked instructions292..295 under one10gas plus actual MSTORE expansion budget, deriving intermediate budgets and exact final gas. It uses the supplied array-length/pointer stack; composition with original allocation, actual bounds and remaining array decoding remain open.


`NativeSourceArrayAllocatedLength` composes38 checked instructions from273 through allocation and length MSTORE295. A single127gas plus actual MLOAD/free-pointer-MSTORE/length-MSTORE expansions budget derives every local budget and exact final gas. The natural allocation bound remains explicit; original bounds, array-loop decoding and exact panic rejection remain open.


`NativeSourceArrayAllocatedLengthFrame` certifies PC296, original remaining stack and global-state preservation after allocation and length storage. Final memory equals the original memory after MSTORE64(newPointer), then MSTORE(allocatedPointer,length), retaining exact write order. Bounds, remaining loop and exact panic rejection remain open.


`NativeSourceArrayLoopSetupDecodes` certifies the pinned instructions296 PUSH32,298 PUSH4,300 DUP2,301 DUP7,302 ADD and303 SWAP4, including both PUSH immediates. These facts do not establish checked execution, bounds or array-loop behavior.


`NativeSourceArrayLoopSetupOperands` certifies six native transitions296..303 with exact PUSH/DUP2/DUP7/ADD/SWAP4 operands and modular ADD. These raw steps do not establish checked stack/gas preconditions, whole-prefix execution or array-loop correctness.


`NativeSourceArrayLoopSetupChecks` derives DUP7/SWAP4 stack and gas prechecks and six checked continuations296..303. Existing PUSH1/DUP2/ADD checks are reused. Full prefix composition, remaining loop preparation, original bounds and exact panic rejection remain open.


`NativeSourceArrayLoopSetupPrefix` composes six checked instructions296..303 to304 under one18gas budget, with exact intermediate gas and PC chains. The modular pointer addition and resulting stack are retained. Remaining loop preparation, original bounds and exact panic rejection remain open.


`NativeSourceArrayEndDecodes` certifies pinned304 PUSH7,306 SHL,307 DUP4,308/309/310 ADD and311 SWAP1, including the PUSH immediate. Checked end calculation, original bounds, loop behavior and panic rejection remain open.


`NativeSourceArrayEndOperands` certifies seven native transitions304..311, retaining SHL operand order, DUP4, modular additions and SWAP1. Raw step facts do not establish checked gas/stack preconditions, array bounds or loop behavior.


`NativeSourceArrayEndChecks` proves seven checked continuations304..311, reusing existing PUSH1/SHL/DUP4/ADD/SWAP1 prechecks. Native SHL operand order and modular additions remain exact. Whole end-calculation composition, calldata bounds, loop and panic rejection remain open.


`NativeSourceArrayEndPrefix` composes seven checked instructions304..311 to312 under one21gas budget, with exact PC/gas chains and native shift/modular-add stack. The end calculation is not replaced by unbounded arithmetic. Calldata acceptance, original bounds, array loop and panic rejection remain open.


`NativeSourceArrayCalldataDecodes` certifies pinned312 CALLDATASIZE,313 DUP3,314 GT,315 PUSH91 and318 JUMPI plus the immediate91. The calldata guard targets the empty-revert block91; allocator panic786 remains a separate obligation. Checked guard execution and acceptance remain open.


`NativeSourceArrayCalldataSteps` certifies checked312 CALLDATASIZE,313 DUP3,314 GT and315 PUSH91 continuations with actual costs2/3/3/3 and precise operands. The branch at318, prefix composition, acceptance bounds and remaining array loop remain open.


`NativeSourceArrayCalldataBranch` proves scanner membership for91 and the checked JUMPI318 with exact10gas and destinations91/319 determined by the supplied native condition. Guard composition, derivation of acceptance and execution of rejection remain open.


`NativeSourceArrayCalldataGuard` composes five checked instructions312..318 under one21gas budget, deriving intermediate mixed-cost budgets and exact final gas. The condition is the native GT of the supplied end against the original environment calldata size. Acceptance bounds and rejection execution remain open.


`NativeSourceArrayCalldataBounds` derives zero/one native GT flags and destinations319/91 from natural end/calldata-size bounds, assuming calldata size fits256bits explicitly. It does not assume a successful branch. Original end bounds remain open; actual empty-revert execution is composed below in `NativeSourceArrayCalldataOutcome`.

`NativeSourceArrayCalldataOutcome` composes the actual five-instruction guard at312 with empty-revert block91..94. An outside natural calldata bound derives rejection; the nine-instruction execution returns exact empty bytes and consumes27gas. The explicit256bit calldata-size bound remains. Original canonical bounds, array loop and allocator panic remain open; CREATE2 admission stays closed.

`NativeSourceArrayLoopEntry` verifies pinned PUSH36/ADD/SWAP2/JUMPDEST at319/321/322/323 and each checked continuation, with exact costs3/3/3/1 and explicit stack bounds. This covers entry instructions only; full array iteration and canonical allocation/calldata bounds remain open. CREATE2 admission stays closed.

`NativeSourceArrayLoopPrefix` composes the four checked entry instructions319..323 into execution reaching324, with exact10gas and the native modular cursor addition36+a. This establishes loop entry only, with no claim of completed iteration or CREATE2 equivalence.

`NativeSourceArrayLoopAccepted` derives guard acceptance from the natural end/calldata-size bound and composes nine checked instructions312..323 to324, exact31gas and output stack. The calldata size must fit256bits explicitly; canonical Market end bounds and full loop iteration remain open. CREATE2 admission stays closed.

`NativeSourceMarketArrayBounds` proves canonical Market calldata size388+128*n and the exact native end calculation352+(n<<7)+4+32 under a nonwrapping256bit size bound. From canonical encoding and length identity it derives the zero guard flag and actual nine-instruction execution to324. Connecting that length/state to the original pre312 decoder chain, allocator bounds and complete iteration remains open; CREATE2 admission stays closed.

`NativeSourceArrayIterationDecodes` verifies pinned DUP2/DUP4/LT/PUSH806/JUMPI at324/325/326/327/330, including the exact two-byte immediate. This establishes instruction decoding only; actual loop execution and complete CREATE2 equivalence remain open.

`NativeSourceArrayIterationSteps` verifies checked DUP2/DUP4/LT/PUSH806 execution at324..327, three gas each, with exact stack transitions and native operand order. Composition, conditional jump330 and complete loop execution remain open. CREATE2 admission stays closed.

`NativeSourceArrayIterationBranch` verifies scanner membership of806 and actual checked JUMPI330, consuming10gas and selecting806/331 from the native condition. Whole guard composition and array iteration remain open; CREATE2 admission stays closed.

`NativeSourceArrayIterationGuard` composes all five checked instructions324..330 and proves exact22gas. The branch condition is native LT(cursor,end), with no assumed outcome. Actual element decoding and full iteration remain open; CREATE2 admission stays closed.

`NativeSourceArrayIterationBounds` derives native LT flags and actual806/331 destinations from cursor/end order, preserving exact stack, execution environment, memory and world across the guard. Full element decoding and iteration remain open; CREATE2 admission stays closed.

`NativeSourceMarketArrayCursor` proves cursor388+128*i, nonwrapping advance by128 and the native continue/finish flags. Its execution theorem runs the actual five-instruction guard for22gas and derives806/331 from index<count, under explicit index/count/256bit-size bounds. This is a guard theorem; complete element decoding and iteration remain open. CREATE2 admission stays closed.

`NativeSourceArrayElementDecodes` verifies all eight pinned element-guard instructions806..816, including PUSH128/PUSH91 immediates and the actual SUB/SLT operations. Checked execution and canonical signed-bound reasoning remain open; CREATE2 admission stays closed.

`NativeSourceArrayElementSteps` verifies checked execution of806..813 with exact costs1/3/3/2/3/3/3, preserving native modular SUB and signed SLT operand order. Branch composition and canonical acceptance remain open; CREATE2 admission stays closed.

`NativeSourceArrayElementBranch` verifies actual checked JUMPI816, scanner-backed empty-revert destination91, fallthrough817 and exact10gas. Guard composition, canonical signed bound and complete element decoding remain open; CREATE2 admission stays closed.

`NativeSourceArrayElementGuard` composes all eight checked instructions806..816 with exact28gas, native modular calldata-size-minus-cursor and signed SLT against128. No branch outcome is assumed; canonical acceptance and complete element decoding remain open. CREATE2 admission stays closed.

`NativeSourceArrayElementBounds` proves exact nonwrapping calldata-size-minus-cursor and signed SLT acceptance when128bytes remain, deriving817. It derives this room from canonical Market encoding and index<count. The explicit calldata size<2^255 bound justifies signed reasoning. Full element decoding and iteration remain open; CREATE2 admission stays closed.

`NativeSourceArrayElementOutcome` proves actual canonical eight-instruction acceptance at817/exact28gas and twelve-instruction short-span rejection with exact empty revert bytes/exact34gas. Rejection follows natural remaining-byte bounds, with explicit signed-size/cursor bounds. Element allocation and full iteration remain open; CREATE2 admission stays closed.

`NativeSourceElementAllocationDecodes` verifies pinned817..825 allocation entry: PUSH64/MLOAD/SWAP1/PUSH128/DUP3/ADD/SWAP1 and both immediates. Actual memory expansion, free-pointer bounds and complete allocation remain open; CREATE2 admission stays closed.
