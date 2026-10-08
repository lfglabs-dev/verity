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
| `block.timestamp`, `block.number`, `block.chainid` | Dedicated transaction-context expressions |
| Ordinary nested root blocks | Ordered recursive lowering with unique local bindings, lexical lookup restoration, and propagated unconditional returns; unsupported nested control flow and statements after return reject with source locations |
| Explicit scalar/tuple return | `returnValues`, preserving order |
| Default scalar locals (development; validation pending) | Uninitialized unsigned integers, address, bool and bytes32 bind a fresh local to zero; reference and unsupported scalar defaults reject at the declaration |
| Scalar local writes (development; validation pending) | `=` and `delete` on materialized scalar locals; converted RHS evaluated before assignment; lexical shadowing retains declaration identity; compound writes and parameter writes reject |
| Invariant scalar `for` (development; validation pending) | uint256 counter from zero, strict `<`, increment by one; literal/parameter/unwritten-local bounds; body return/revert preserved; body counter writes, mutable bounds, break/continue reject |
| Schema ABI array-length `for` (development; validation pending) | Memory/calldata array length captured after its exact initial decoder; recursively checked body preserves memory headers; memory writes and external calls reject |
| Local declarations and storage aliases | Bindings named after the Solidity local (suffixed `_1`, `_2`, ... on collision), or resolved read paths |
| Scalar storage reads, `=`, and `delete` | Resolved uint8–uint256, address, bool, and bytes32 fields; exact solc slots and packed offsets; masked writes preserve neighboring bits and bool reads/writes normalize to 0/1 |
| Root fallthrough, bare `return;`, and named root return parameters | Void roots emit `stop` on fallthrough or bare `return;`; roots whose return parameters are all named scalars initialize each to zero, allow body reads/writes, and emit `returnValues` on bare `return;` or fallthrough; empty-body scalar hooks return zero words |
| One/two-key mappings to structs | solc slots, word offsets, and packed uint offsets |
| One/two-key scalar mappings | address/uint256/bytes32 keys; uint8–uint256, address, bytes32 and bool values; root assignment and `delete`, with masked narrow writes |
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
| `require(condition, "message")` | Exact `Error(string)` bytes; UTF-8 literal messages, including empty strings, in roots and inlined helpers |
| `require(condition, CustomError(args))` and `revert CustomError(args)` | Resolved static unsigned/address/bool/bytes32 errors; arguments restricted to decimal numeric literals or scalar bindings; exact selector and ABI words (`revert CustomError(args)` lowers to `.requireError (.literal 0) name values`) |
| Narrowing casts | Bit masks, not overflow checks |
| Ternaries | Lazy `ite` branches |
| Resolved acyclic helper calls | Inlined single-value, void, and multi-return internal/private bodies with separate local scopes, including C3 virtual override resolution across `linearizedBaseContracts`, diamond `super.fn(...)` resolution, explicit base-qualified `Base.fn(...)` calls, and empty-body scalar virtual hooks |
| ABI encoding and Keccak (experimental) | `keccak256` over static scalar `abi.encode`, a single complete supported root struct, literal byte buffers and `abi.encodePacked` of unsigned/address/bool/bytes32 scalars and admitted byte buffers. Packed buffers preserve exact byte widths and lengths using aligned word memory; nested buffers receive separate allocations. Hex numeric literals retain their exact value. Dynamic byte parameters, arbitrary byte locals, direct packed structs, signed/fixed-byte widths other than bytes32 and effectful scalar arguments remain rejected. The focused 96-case A/B/C campaign includes unmodified pinned `IdLib.toId`, storage/events and rollback. All four generated variants agree, 15 semantic mutants are detected with minimized witnesses, and 11 located rejection/acceptance controls pass on captured local snapshots. Copy-loop and packed-allocation helper proofs are in `AbiMemory`; exact-head release gates remain pending. |
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
