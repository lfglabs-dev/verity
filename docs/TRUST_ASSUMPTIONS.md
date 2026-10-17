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

The entry-point invariant infrastructure in
`Compiler/SolidityImport/EntryPointInvariants.lean` composes actual
`Transactions.executeBody` steps with explicit bindings, effective model
fields and custom errors. It proves rollback and finite-sequence invariant
preservation from per-public-entry obligations; environment preparation and
frame reset have explicit preservation premises. It introduces no project
axiom. It does not establish the ABI/dispatch boundary, deployment, value
transfer, loop correctness, reentrant external-call correctness, or a
Midnight invariant. Instrument errors are excluded by successful `Except`
observations, rather than treated as Solidity reverts.

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
`.lake/solidity-import/solc-0.8.34` or `.lake/solidity-import/solc-0.8.10`.

The frontend is in the trust base. A covered model is not a proof that the
model matches the Solidity source or solc's bytecode. `storageLayout` slots and
packed offsets are copied from the pinned solc release selected by `Profile.solc`
(`0.8.34+commit.80d5c536` or `0.8.10+commit.fc410830`; linux-amd64 and
macosx-amd64 SHA-256 pins in `Import.lean`). Because `solc 0.8.10` lacks
`--no-import-callback` and silently ignores unknown standard-JSON settings such
as `"viaIR"`, the importer rejects `viaIR := true` on `0.8.10+commit.fc410830`,
restricts `evmVersion` to pre-Paris releases up to `"london"`, and verifies that
every key in `parsed["sources"]` was explicitly collected into the hashed
standard-JSON input. `mappingSlot` in the denotation oracle is not Keccak. Numeric
claims are about the values `structMember` reads back.

Checked `uint256` and narrower unsigned arithmetic is lowered to `Stmt.ite` plus
`Stmt.panic`, not to a second interpreter. Explicit `uint128(x)` is truncation
(`bitAnd` with `2^128-1`). Ternaries are `Stmt.ite`, so the untaken branch is
not evaluated. Library helpers and inherited contract helpers in an accepted
acyclic slice are inlined: unqualified internal/private calls in the target
contract's `linearizedBaseContracts` resolve to the most-derived implemented
override in the same transitive `baseFunctions` family, `super.fn(...)` resolves
across the C3 suffix after the calling contract, and explicit `Base.fn(...)`
calls verify base membership and static declaration ownership. Void internal/private
helpers are inlined via continuation-passing so nested early `return;` inside
`if`/`else` runs the post-conditional continuation only on fallthrough paths
with restored lexical scope. `revert CustomError(...)` lowers through the same
static custom-error encoding as `require(false, CustomError(...))`. Scalar `bool`
storage fields use 8-bit packed storage with `logicalNot (logicalNot ...)`
normalization on read and write, and prefix `!` on `bool` lowers to `logicalNot`.
Root functions whose return parameters are all named scalars initialize each to
zero and return them on bare `return;` or fallthrough, while empty-body scalar
hooks return zero words. Modifiers with a single top-level `_;` (without `virtual`
or internal `return;`) are inlined around root and helper bodies with their own
lexical scope and `unchecked := false`, wrapping multiple modifiers outside-in;
when a modifier has statements after `_;`, return values on explicit return or
fallthrough paths are captured before running the post-placeholder statements.
Internal function-pointer locals initialized at declaration to a direct
internal/private helper or a conditional `cond ? f : g` over internal/private
helpers evaluate any selector condition once at declaration, reject reassignment,
and lower calls by inlining the target helper(s) after evaluating arguments once in
caller source order. Whole-struct `delete` on one/two-key mapping structs clears
every decoded scalar/packed member to zero after rejecting structs with `opaque`
or array members.
`UncheckedBlock` switches unsigned `+`, `-`, `*` and `+=`/`-=` within its lexical
block to wrapping `2^bits` arithmetic while preserving division/modulo-by-zero
panics and resetting across call boundaries. Scalar assignment expressions
`(x = rhs)` require order-independent binary siblings and single-argument call
contexts. Unnamed multi-return scalar helpers are inlined via continuation-passing
into fresh zero-initialized result bindings and consumed only by matching tuple
destructuring declarations or assignments (evaluating converted components before
committing non-elided local or scalar storage targets and rejecting duplicate
targets). Unsigned scalar parameters modified by `+=` or `-=` are copied into
declaration-bound local bindings at frame entry so call-by-value compound updates
remain frame-local. Narrow `.uintN bits` event parameters accept canonical integer
constant literals `n < 2 ^ bits` alongside matching direct parameters. Full-width
`int256` scalar parameters, locals, returns, storage fields, and mapping values use
two's-complement 256-bit words (`slt`/`sgt`/`sdiv`), with `Panic(0x11)` on checked
signed `+`, `-`, `*`, `/`, and unary `-` overflow (including `-type(int256).min` and
`type(int256).min / -1`) and wrapping two's-complement arithmetic inside
`UncheckedBlock` (preserving division-by-zero `Panic(0x12)`). Contract/interface
and `address payable` scalar values use 160-bit address representations for
parameters, locals, returns, storage fields, mapping values, and explicit
`Contract(addr)` / `address(contractVal)` casts. Empty-body root functions without
modifiers that return a single `T[] memory` (`T` in `uint256`, `int256`, `address`,
`bool`, `bytes32`) emit `Stmt.returnValues [.literal 32, .literal 0]` (the 64-byte
ABI encoding of an empty dynamic array); root `bytes calldata` parameters (named or
unnamed) use `AbiLowering.bytesCalldataHead` under `.explicitPrelude` to validate
the offset, header, `uint64` length bound, and payload tail bound at entry and
expose `.length`. Same-contract overloaded function declarations are accepted in
`refInt` when every candidate in `overloadedDeclarations` belongs to the same
virtual family or shares an origin declaring contract across `baseFunctionClosure`,
while cross-contract unrelated overloads and duplicate root function names in a
single slice are rejected. Custom-error arguments accept pure compile-time
constant scalar expressions (`address(0)`, `type(T).max`/`min`, and named numeric
constants) that lower to canonical literals with empty preludes alongside direct
scalar bindings and literals. Conditional tuple expressions (`cond ? (...) : (...)`)
in tuple declarations and assignments convert leaf components to the target types
and join branches through fresh temporaries and `Stmt.ite`, rejecting stateful or
assignment tuple components. Single-assignment inline assembly supports `tload(slot)`
via `Expr.tload` over `DenoteState.transientStorage`. Fixed-size unsigned scalar
array members inside mapping structs (`encoding == "inplace"`, `byteOffset == 0`) are
expanded on demand into synthetic `StructMember` entries with `Panic(0x32)` bounds
guards on element reads, writes, `delete`, and memory snapshot copies, and unnamed
root fixed-size scalar array returns (`T[L] memory`) lower to `L` ABI return words.
`msg.data.length` and `_msgData().length` lower to `Expr.calldatasize`, and
zero-parameter root functions returning `msg.data` or `_msgData()` emit
`Stmt.returnValues [.literal 32, .calldatasize, .calldataload (.literal 0)]` with
`returns := [.bytes]`. Solidity `enum` types (`1..256` members) lower to `.uintN 8`
scalars with tighter `< members.size` root calldata entry guards, `Panic(0x21)`
bounds checks on explicit `Enum(x)` casts from integer types, and `0` / `members.size - 1`
bounds for `type(Enum).min` / `type(Enum).max` (while rejecting fallible `Enum(x)`
casts inside `abi.encode` / `abi.encodePacked` and `enum` struct or storage members).
Unsigned exponentiation (`**`) lowers to `Expr.externalCall "exp" [a, b]` (masked to
`2^bits - 1` when `bits < 256` in `unchecked` mode, and guarded by `maxSafeExponent`
or `maxSafeBase` with `Panic(0x11)` in checked mode when either base or exponent is a
canonical literal, rejecting checked dynamic-base-and-exponent `**`). Bit shifts
(`<<`, `>>`), bitwise `&`, `|`, `^`, unary `~` (masked to `2^bits - 1` on narrow
`uintN`), and compound assignments (`<<=`, `>>=`, `&=`, `|=`, `^=`, `/=`, `%=`) lower
to `.shl`/`.shr`/`.sar`/`.bitAnd`/`.bitOr`/`.bitXor`/`.bitNot` and checked division/modulo
helpers, and single-assignment inline assembly supports `sub`, `div`, `mod`, `and`, `or`,
`shl`, `shr`, `sar`, `gt`, `eq`, `iszero`, `not`, and `clz` (lowered as an 8-step binary
search over `[128, 64, 32, 16, 8, 4, 2, 1]` returning `256` on zero, including `UtilsLib.zeroFloorSub`
and `BitMapLib.msb`). Bounded unsigned `while` loops on a writable `uintN` local `v` (`v != 0` /
`v > 0`) ending with a strictly decreasing bit-clearing (`v &= v - 1` or `msb(v)` + `clearBit`)
or positive constant right-shift (`v >>= k`) update lower to `Stmt.forEach` with bound `bits`
and per-iteration condition check, and `memory`/`calldata` struct locals and `calldata`-to-`memory`
struct conversions materialize schema-checked structs and struct-array elements into memory
while rejecting `memory`-to-`calldata` conversions, reassigned struct locals, and `immutable`
state variables. Root and helper `T[] calldata` / `T[] memory` scalar array parameters
(`uint8`–`uint256`, `int256`, `address`, `bool`, `bytes32`) validate ABI heads, `uint64` lengths,
and `32 * length` tails via `AbiLowering.scalarArrayCalldataHead` / `scalarArrayMemoryHead`,
materialize `calldata`-to-`memory` helper arguments via `materializeCalldataScalarArray`, and
enforce `Panic(0x32)` bounds checks and calldata element validation on `arr[i]` via
`readScalarArrayElement`. Root and helper `bytes calldata` / `bytes memory` and `string calldata` / `string memory`
parameters and non-reassigned `bytes memory` / `string memory` locals decode via
`bytesCalldataHead` / `bytesMemoryHead` and retained `(pointer, size)` byte buffers
(`byteBuffers` / `stringBuffers`), supporting `.length` on any `bytes` buffer (`b.length`,
`bytes(s).length`, and inline `abi.encode*` / `bytes.concat` expressions), `bytes calldata`-to-`bytes memory`
local and helper-argument copies, `bytes.concat` / `string.concat` (lowered via `lowerPacked`),
`abi.encodeWithSignature` (computing the 4-byte `keccak256` signature selector prefix and
concatenating `32 * n` scalar argument words via `encodeSelectorAndWords`), `abi.encodeCall`
(resolving the target `FunctionDefinition` selector via `lowerMemberFunctionSelector` and
converting the argument tuple components to their declared parameter types), and single-return
`bytes memory` / `string memory` helpers (`inlineStringFn`). Unnamed root functions returning
`bytes` or `string` (`functionDynamicBytesReturn?`) lower admitted byte/string return expressions
(`canLowerDynamicBytesReturnExpr`) via `lowerEncodedBytes` into `_verity_memret_<stem>` bindings
and `Stmt.returnBytes`, reading 32-byte words from memory and right-zero-padding the final partial
word (`32 :: length :: paddedWords`) in both `Denote.returnBytesWords` and `Compile.compileStmt`.
`address(this).balance`, `payable(address(this)).balance`, and Yul `selfbalance()` lower to
`Expr.selfBalance`, and `tx.origin` and Yul `origin()` lower to `Expr.txOrigin`, while external
`<addr>.balance` reads and `tx.gasprice` are rejected.
`UtilsLib`-style `min` is the Yul term `xor`/`mul`/`lt`, not a renamed `Expr.min`.
Generated scalar bindings are hygienic, and helper-local bindings are scoped.
Only reached storage fields are decoded; state variables whose label appears
multiple times in `storageLayout.storage` (such as shadowed private state
variables) are rejected when referenced, while unreferenced duplicate private
`__gap` arrays do not block import. Namespace-qualified output names and
framed-JSON provenance are deterministic. Unnamed non-empty root fallthrough, named call
arguments, external contract calls, external or reassigned function pointers, and narrow signed types are rejected.
The slice makes no dynamic ABI-head claim: that unrelated denotation extension
is not part of this change. Solidity sources are Lake inputs only when the
consumer declares them (`input_dir` + `needs`); consumers should also
re-elaborate in CI to verify freshness against a compiled import.

## CI execution and Action supply chain

GitHub Actions and the machines that execute them are operational trust
boundaries, not part of the Lean proof kernel. Every external Action reference
under `.github/` is pinned to a full commit SHA; local composite Actions remain
reviewed repository code. Repository policy rejects mutable external Action
tags, gives workflows read-only default token permissions, and requires manual
approval before workflows from every external fork contributor may run.

Self-hosted runners remain trusted infrastructure. Pull-request code is
untrusted even after approval and must not share credentials, writable data, or
network reachability with production services. These controls reduce Action
supply-chain drift and accidental execution; they do not make a persistent
self-hosted runner a security boundary.

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
- **Status**: 1 documented axiom in [AXIOMS.md](AXIOMS.md): `solidityMappingSlot_injective` (collision-resistance of `keccak256(abi.encode(key, base))` for in-range base slots and keys `< 2^256`, not keccak injectivity on all inputs; the range hypotheses are required because the ABI encoding reduces its arguments modulo `2^256`, so the former unbounded statement was inconsistent). The mapping-slot *range* axiom has been eliminated via the kernel-computable Keccak engine. Selector computation is kernel-computable, the Layer 2 generic body-simulation axiom has been eliminated, and the Layer 3 dispatch bridge remains an explicit theorem hypothesis rather than a Lean axiom.
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
- **Fork dependency**: Verity pins [`lfglabs-dev/EVMYulLean`](https://github.com/lfglabs-dev/EVMYulLean), a fork of [`NethermindEth/EVMYulLean`](https://github.com/NethermindEth/EVMYulLean). The pinned commit is recorded in `lake-manifest.json` under the `evmyul` package. The exact divergence from upstream is enumerated in [`artifacts/evmyullean_fork_audit.json`](../artifacts/evmyullean_fork_audit.json), regenerated by `scripts/generate_evmyullean_fork_audit.py` and validated by `make check`. The current pin is 25 commits beyond the recorded upstream base and includes two explicitly scoped implementation/transition changes: a structurally recursive jump scanner and an Osaka CREATE/CREATE2 collision/storage correction. They are audited in [`docs/EVMYULLEAN_FORK_SCOPE.md`](EVMYULLEAN_FORK_SCOPE.md), with exact-head native/mutation/real-EVM component evidence in [`artifacts/evmyullean_osaka_creation_reference.json`](../artifacts/evmyullean_osaka_creation_reference.json). Upstream conformance does not transfer to these changes by ancestry. The generator rejects any other semantic commit and binds the scope to immutable commit/evidence identities. Whole-creation wrapper fuel/gas, postcreation account correspondence and whole-function differential validation remain separate obligations. In addition to the `make check` validation, a weekly scheduled GitHub Actions workflow ([`.github/workflows/evmyullean-fork-conformance.yml`](../.github/workflows/evmyullean-fork-conformance.yml)) runs `make test-evmyullean-fork`, which re-verifies the fork audit artifact against `lake-manifest.json`, checks the EVMYulLean native lowering report, rebuilds the native transition harness, rebuilds the public EndToEnd EVMYulLean target, and rebuilds the native builtin routing lemmas together with the native bridge smoke tests and 0 concrete bridge tests, surfacing any upstream drift as a red workflow plus an automatically opened or updated GitHub issue for scheduled/manual failures.
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
  mappings (`addr` / `transient` / `map` / `mapUint` / `map2` /
  `mapChain` / `transientMapChain`) through
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
  unchanged. `AdversaryModel.withLinks` / `ExecutableCallContext.withLinks`
  extends this to state-changing sites: a linked `.call` site runs the body
  in `Contract.hopCall` at the target (success commits the post-hop state,
  with one caller-controlled journal entry; a reverting body answers
  `.revert []`, so the typed call reverts with the caller state restored).
  Fidelity: `Contracts.externalCallContractWordsTo_withLinks`,
  `Contracts.externalCallEffectWordsTo_withLinks`,
  `Contracts.externalStaticCallContractWordsTo_withLinks` (each with
  `_revert`). The hop installs `msgValue := 0` (typed interface calls carry
  no value). Unlinked mutable sites are still answered by the base
  adversary. Compilation-model lowering is unchanged.
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
- **Runtime-target dispatch and G25 (one interface, several runtime
  contracts)**: a bound hop always runs at the call's runtime target
  address. A receiver named after a binding selects it; otherwise the
  interface's bindings decide: one binding, or several bindings that all
  resolve to the same callee contract, run that callee's body at the
  runtime target (two tokens of one contract type stay distinct through
  per-address namespacing); several `deferred` bindings use the deferred
  lowering; bindings to different callees, or a mix of named and `deferred`
  bindings, **fail closed** at elaboration. **Trust boundary (author rule)**:
  a named binding asserts that every target of that interface holds the
  named contract. If one interface is called on addresses that hold
  different contracts, use `deferred` and instantiate the context with
  `withLinks` (or `withViewLinks`) keyed by target address
  (`links "IFace.method" target`).

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
slot is not itself keccak-derived) and `MappingBasesInRange` (declared
mapping base slots are below 2^256, as the bounded
`solidityMappingSlot_injective` requires) — hypotheses discharged per
contract, not axioms. Under that invariant the lens read equals the
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
  `"fail"`). These are closed Lean definitions, not feature-flag, env-var, or
  backend overrides. Supported single-word results decode that same word;
  aggregate and no-result stubs use their inhabited default. Executable-plane
  theorems about call *outcomes* are therefore claims about the stub, not about
  a real callee; adversarial reasoning lives in the model plane
  (`DenoteExternalCalls`).
- **`ExecutableCallContext.ofAdversary` pins `target = 0` and `value = 0`.**
  It is a convenience context, not a general linker: a nonzero target or value
  requires `ofCallEnv` or a custom `resolve`. The generated registry predicate
  does not depend on it: each `*_entrypoint` existentially quantifies the
  executable resolver, so a transition produced by any `ExecutableCallContext`
  carrying the registry adversary (including `ofCallEnv`) is a registered
  transition. `CallbackBounded` therefore covers executable linked calls that
  resolve a nonzero target/value, not only the zero boundary.
- **Registry callback calldata is compiled-dispatch ABI, not the journal
  encoder.** Generated `*_entrypoint` predicates constrain
  `CallbackContext.calldata` with `abiEncodeDispatchArgs` /
  `ToDispatchVal` (offset/length/packed-bytes layout matching
  `genParamLoads`). `ExternalArg.toWords` remains the executable journal
  encoding and is not an ABI decoder. Public `calldatasize`/`calldataload`
  stay deterministic stubs (`0` and the offset); generated `*_registry`
  bodies rewrite those intrinsics to `calldatasizeLive`/`calldataloadLive`,
  which read `ContractState.calldata` installed by `withCallbackContext`.
- **`externalCallWords` (pure expression form) does not journal.** It is not
  monadic, so `externalCall name [args]` used as a pure expression remains
  observationally silent; only the monadic forms journal. Specs that need
  call observability must use the monadic primitives.
- **`callExternal name(args)` surface** remains an unmodeled no-op at this
  plane.
- **Hashed mapping accessors are executable, on a symbolic channel.**
  `getMappingN`/`setMappingN`, `getMappingWord`/`setMappingWord` and the
  generated `structMember`/`setStructMember` family read and write
  `StorageKey.mapChain baseSlot keyWords wordOffset`
  (`ContractState.readMapChain`/`writeMapChain`); `transient` mapping chains
  use `StorageKey.transientMapChain baseSlot keyWords`
  (`readTransientMapChain`/`writeTransientMapChain`).
  `structMembers`/`structMembers2` destructuring lowers to those reads.
  Entries with different `(baseSlot, keyWords, wordOffset)` are independent
  by constructor injectivity, and the channel is disjoint from the scalar
  `.slot` channel and from the `storageMap`/`storageMapUint`/`storageMap2`
  channels behind `getMapping`/`getMappingUint`/`getMapping2`, so executable
  plane non-aliasing (key vs key, member vs member, mapping entry vs scalar
  slot) uses no axiom. The Solidity keccak slot
  (`Compiler.Proofs.mappingChainSlotLocation`: keccak folded over the key
  path plus the word offset modulo `2^256`) is an interpretation: the
  executable channel agrees with the flat `.slot` channel the model plane
  reads under `Compiler.Proofs.Storage.HashedMappingLayout.HashedCoherentOn`,
  preserved by aligned writes given a finite layout non-alias certificate
  (a hypothesis, not `solidityMappingSlot_injective`). A field is accessed
  through exactly one family, fixed by its declared storage type. Hops
  namespace both hashed keys per contract (`StorageKey.scoped`), and
  `Contract.run` rollback restores them with the rest of `storageWords`. The
  pure expression form `structMembers` outside `let (..) :=` / `return` still
  yields `default`.
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
`if tload(lockSlot) { revert(0, 0) }; tstore(lockSlot, 1)` pair runs
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
Yul decision `if tload(slot)` (nonzero is true) agrees with the model's `lock ≠ 0` for every
stored lock value, not only the binary `{0,1}` acquire/release cycle. `Compiler.Proofs.IRGeneration.SpliceSimulation` now proves the full guarded
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
     macro-emitted entrypoint registry (`entrypointRegistry` and per-function
      `*_registry` / `*_registry_unguarded` executables generated by
      `verity_contract`) is the source of this list on the macro path.
      Registry-mode `linked_contracts` hops use the bound callee's `*_registry`
      executable (and thread the current `ExecutableCallContext`) when that
      definition takes the context, including view/static callees whose public
      bodies do not open a reentrancy window. Public hopCall bodies keep the
      ctx-free public definition. Generated `*_entrypoint` predicates require
      Lean arguments to match compiled-dispatch ABI words of
      `CallbackContext.calldata` (`abiEncodeDispatchArgs` into
      `dispatchCalldataMatches`); `receive` is registered only for empty
      calldata. Registry-mode executables observe that same calldata through
      `calldatasizeLive`/`calldataloadLive`, including the selected
      entrypoint selector at `calldataload 0` (`CallbackContext.selector` /
      `ContractState.selector`). `dispatchCalldataMatches` accepts
      `genScalarLoad`-normalized noncanonical Bool / uintN / address words.
      `FixedArray` encodes as a length-free composite (tuple of members);
      source `Tuple` encodings are flattened before `abiEncodeDispatchArgs`.
      Helpers whose bodies (transitively) read `calldatasize`/`calldataload`
      are routed through `*_registry` so they observe live calldata.
      Completeness of the generated
      list is still an author obligation: the kernel checks consumers of
      `entrypointRegistry`, it does not independently re-enumerate compiled
      dispatcher cases. Same-contract `selfCall` hops keep the guarded public
      / `*_registry` path so they still observe the nonReentrant tload
      prologue. The Lean toolchain is pinned by `lean-toolchain`;
      `threadAdversaryThroughExecutableSyntax` consults no IO or env vars.
      Existing `unsafe qualifiedTupleBindTypedLocals` is elaborator-only
      typed-local inference, not a kernel skip.
     Author-supplied lists remain only for hand-written `ReentrancySpec`
     consumers.
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

Solidity logical `&&`/`||` imports use `Stmt.ite`, whose selected-branch
semantics is pinned in `SolidityImport.Coverage`. They do not use the eager
model logical operators. Differential fixtures compare skipped and executed
guards, mapping accesses and helper calls against solc, plus conditional and
De Morgan variants. This is tested lowering, not a Solidity semantics proof.

### Imported scalar ABI entry guards

Scalar `uintN`, address and bool parameters now receive entry checks against
raw calldata words, before any source statement. Parameter cleanup alone is
not validation. Failed guards use the fresh EIP-211 return-data buffer, which
is empty at external-call entry; `Denote.returndata_withTransactionContext`
pins that initialization. Imported functions record this low-level boundary
as the explicit `solidity_scalar_abi_entry` local obligation with status
`unchecked`: differential evidence is not a Lean proof of solc equivalence.
The compiler's unsafe-boundary validation remains enabled. Semantic coverage
pins the calldataload arm and the exact revertReturndata bytes arm; it does not assert
correctness of arbitrary use of returndata after external calls.

The raw-word ABI probe includes public Denote parameter binding as well as
actual solc and Verity bytecode. This instrument currently covers complete
scalar words; it does not establish dynamic-struct or partial-byte calldata
validation. The existing stateful scalar runner supplies the same argument
words as calldata when executing imported entry guards.

The ABI observer also executes the same bound frame and reads its actual
return/revert bytes, checking public `denoteFunction` status and successful
return words against that frame. `revertReturndata` now preserves the actual
word buffer as `revertWithData` bytes; the observer never synthesizes empty bytes for an
unclassified Denote failure. The existing returndata representation is word-based; arbitrary partial-byte
external returndata is outside this entry-guard instrument. The scalar probe rejects unexpected binding
failure and therefore cannot silently reinterpret a missing semantics arm as
an ABI rejection.

Scalar guard positions use the sum of preceding model ABI head sizes, not
source parameter ordinals or one word per model parameter. Flat structs whose
members all have supported scalar types use the full tuple ABI, including
unused fields. Public Denote binds their indexed fields with the same head
layout as the compiler. Memory parameters validate all narrow fields before
source execution; calldata parameters validate a narrow field at its read.
This preserves which revert wins when a source `require` precedes that read.
The A/B/C fixture exercises this distinction with noncanonical words, and the
binder has separate kernel-checked flat/nested offset and rejection witnesses.
These finite checks are not a general solc ABI-decoder equivalence proof.

The importer currently lowers only flat scalar structs through this full ABI
path. Nested structs, arrays, dynamic `Market` parameters and partial-byte
calldata remain outside it. Dynamic structs use the experimental explicit-prelude boundary described
below; historical scalar projections are no longer an import fallback. Read-time guards use the empty returndata buffer
within the present fragment, which has no external calls; adding external calls
requires an explicit empty-revert lowering that cannot inherit stale returndata.

### Experimental explicit source ABI preludes

`FunctionSpec.abiDecoding` now distinguishes the default generic decoder from
an explicit source-compatible prelude. `params` remains the complete ABI
signature in both modes; `bindingParams` is empty only for an explicit prelude.
The compiler and Denote therefore execute the body's raw-calldata checks before
any conflicting generic dynamic-tuple check. SourceSemantics uses the same
binding policy. This is an explicit trust boundary, not a solc equivalence proof.

Compilation requires a `solidity_explicit_abi` local obligation, rejects internal
functions and automatic locks in this mode, and checks the body against an empty
parameter scope as well as the ordinary signature scope. Body locals cannot
silently refer to unloaded parameters or shadow declared signature parameters.
The generic SupportedFunction profiles now require the standard ABI policy;
explicit-prelude compiler correctness needs a separate decoder proof. Updating
the consumers preserves the existing standard-policy theorem conclusions.
The complete `Verity Contracts SolidityImportSmoke` library build now passes in
this experimental checkout. That establishes elaboration compatibility, not
correctness of the explicit decoder or completion of its validation gates.

The experimental importer now uses the checked AST schema and explicit ABI
prelude for dynamic struct roots, retaining every member in the declared ABI.
The legacy scalar projection fallback has been removed: an unsupported schema
fails at its original AST node. Complete memory structs, scalar arrays and flat struct arrays are
materialized before source statements; calldata scalar members and array
headers are checked at reads. Computed array indices and mixed static/dynamic
struct parameter lists remain rejected until their ordering/loading is covered.
The imported ten-function pinned Market fixture passes 340 A/B/C controls,
including eager/lazy address checks and malformed array payloads. Scalar-array
and two-dynamic-root fixtures pass 96 and 132 controls respectively. Their
three, four and four equivalent variants pass strict observation comparisons;
the corrected Market generated-name collision additionally checks that all five
memory decoders rename the colliding temporary. Twenty runtime lowering mutants
have successful positive controls and reproduced deletion-minimal divergences.
The permanent axiom audit includes the bounded full-state smoke proofs, which
use only `propext` and `Quot.sound`. These are working-tree preflight results,
not exact-head merge receipts. They do not establish arbitrary nested types,
partial-byte Denote inputs, whole Midnight support, general decoder correctness
or completion of the required publication gates.

The legacy function-correctness lemmas explicitly require the standard decoder
when their statements assume automatic binding of declared parameters. Supported
function profiles supply this fact; it is not inferred from the ABI signature.
Structural metadata lemmas continue to retain the full signature under either
policy, while guarded body-shape lemmas use the parameters actually loaded.
The same standard-policy prerequisite is explicit in the generic dispatch and
contract-correctness wrappers. Their supported-profile callers derive it from
the function inventory. Native body-shape lemmas use the actual loaded parameter
list; an empty declared list remains empty under either policy. Whole-library
compilation passes, including the end-to-end native examples. The bounded smoke
proof checks every decoder instruction and the entire resulting state, avoiding
a single large kernel reduction. These results do not establish a general
correctness theorem for the explicit decoder, which remains a separate proof
obligation.

Imported scalar event declarations feed both compilation and the stateful
observer. Denote retains source-order event arguments; `SequenceRunner` performs
ABI scalar cleanup and partitions indexed topics using the imported declarations,
with Keccak of the canonical event signature. This observer encoding is tested,
not a proof that Denote's legacy event representation is already EVM log bytes.
Anonymous/dynamic event encodings and arguments with guards or effects fail
closed. Existing backend restrictions on direct narrow parameters remain intact.

### Solidity importer bounded-loop proofs

The indexed invariant rule in `Compiler/SolidityImport/LoopInvariants.lean`
is proved by induction over Denote's actual bounded-loop executor. It requires
body preservation after index binding, initial-state validity, and an explicit
postcondition for every early-exit outcome. Its `.forEach` corollary also
requires successful count evaluation. Unclassified interpreter failure is
not identified with an empty EVM revert. These kernel-checked theorems add no
axioms, source-loop lowering, EVM correspondence, gas guarantee or assumption
of callback correctness. Concrete smoke proofs cover storage writes and exact
panic propagation; they do not prove Midnight's whole-contract invariants.

### Stateful source ABI identity and ordinary blocks

The Solidity import sequence adapter checks that canonical source calldata words
and the four-byte selector agree with transaction metadata. It resolves selectors
from complete model signatures, rejects ambiguous dispatch, and uses the public
external-parameter decoder with the full transaction context. A malformed ABI
payload produces the contract's empty revert; inconsistent harness metadata is
a harness error. Traced status and successful return bytes are checked against
public Denote execution; exact revert bytes, touched slots, rollback and events
are compared through the A/B/C harness. These executable checks do not constitute
a general proof of importer or decoder correctness.

Ordinary root blocks flatten into existing ordered model statements. The importer
restores lexical lookup maps while retaining globally fresh binding names and
propagates unconditional returns; it still rejects unsupported nested constructs.
This introduces no new Denote primitive or trusted axiom. Composition fixtures
exercise dynamic ABI decoding, lexical scopes, writes and indexed events, including
rollback and aliased ABI offsets. The block-effect deletion mutant must produce
a reproduced deletion-minimal runtime divergence.


### Internal root-struct reference arguments

The importer distinguishes scalar helper arguments from root memory/calldata
references. Same-declaration, same-location helper parameters reuse the source
root descriptor (including ABI head and memory stem); they do not allocate a
copy or synthesize a projected scalar. Helper exit restores caller bindings.
Cross-location copies, storage references and unsupported subobjects remain
located rejections. Existing restrictions on helper effects and single returns
remain in force. No Denote semantics or proof axiom is added by this lowering.
The source-EVM-first corpus checks eager/lazy validation, dirty unused members,
independent and aliased roots, nested/library calls, storage, events and revert
bytes. The wrong-root mutation must compile, diverge and produce a minimal
transaction witness. These differential checks do not constitute a general
proof of Solidity memory aliasing or a full-Midnight equivalence theorem.

External library reference calls are rejected before helper inlining: their ABI/
delegatecall boundary cannot share a caller descriptor. Memory helper parameter
names mask caller scalar Yul bindings; raw pointer use remains unsupported.
Mutations removing this masking, the external-call guard and the location guard
must first admit the unsupported source, then fail the located rejection suite.
A compiler or harness error never counts as mutation detection.


### ABI encoding and packed Keccak buffers (experimental)

The new encoding lowering consumes complete admitted schemas; it does not
recognize IdLib names or substitute a market-member projection. A dynamic root
is encoded with its top-level offset, tuple heads and inline array element
words. Memory arrays of structs contain pointers on input and inline words in
the encoded output. Calldata fields are checked when consumed; memory fields
were checked when the root was materialized.

Keccak uses the existing DenoteOracle.keccakMemorySlice boundary. The concrete
A/B/C adapter hashes bytes reconstructed from word chunks. Packed lowering
therefore allocates separate buffers, initializes output words to zero, and
inserts each byte with aligned mload/mstore and shifts. It never assumes the
word-memory model implements overlapping unaligned EVM stores. The arithmetic
lemmas in AbiByteLanes prove that insertion into a zero byte lane preserves
all other byte lanes, yields the selected byte, and stays within the EVM word
bound. AbiMemory proves the complete actual copyBytes statement for local buffer
pointers and start/index bindings, including all iterations, empty copies and
source preservation under disjointness. It proves the complete packedBuffer
reserve-and-clear sequence for a stable local size binding, with exact memory
including the free-pointer write at64. Both proofs require explicit freshness,
alignment and allocation bounds. The proof extracts the actual emitted copy
body rather than maintaining a second lowering. The oversized nonwrapping
reserve case also proves exact Panic(0x41) bytes. The wrapped-addition reserve case proves the same exact panic payload.
Integration of these local obligations across the full importer remains a
separate obligation; no solc equivalence proof is claimed.

The focused differential compares exact outputs to independent eth_abi and
eth_hash calculations as well as all three execution routes, including the
85-byte IdLib outer preimage and prefixes spanning word boundaries. The two
vendored hashing dependencies are exact files from Midnight96d31343, recorded
in hashing-provenance.json. No pilot golden or pilot provenance is changed.
These focused results are not full Midnight import coverage or release gates;
the focused mutation, generated-equivalent and rejection campaigns have local
receipts, but complete representation proof obligations and exact-head release
validation remain pending for this family.

Solidity `if`/`else` imports use `Stmt.ite`, whose selected-branch semantics
is pinned in `SolidityImport.Coverage`; root returns inside a branch rely on
`Stmt.returnValues` stopping execution in both Denote and compiled Yul.
Helper conditionals are restructured so that exactly one branch computes the
inlined result; locals remain immutable single-assignment bindings, so no
branch can update state visible to the other. Differential fixtures compare
early returns, nested and chained conditionals, branch-local guards and
storage/mapping effects against solc, plus inverted-branch and ternary
variants. This is tested lowering, not a Solidity semantics proof.

### Numeric literals and units (development)

Decimal, hexadecimal and scientific literals are parsed into exact natural
numerator/denominator pairs; digit separators are removed and a missing whole
part in leading-dot fractions means zero. Time/currency scaling occurs before the integral
check, so fractional amounts such as 0.5 hours retain their exact value. No
floating-point arithmetic is used. Nonintegral results, oversized runtime words
and unsupported constant expressions reject with source locations. Named unsigned/bool constants resolve by declaration ID and their initializers
use the same exact lowering. General rational constant-expression evaluation
remains unsupported. Sums of exact natural constant operands are evaluated with
unbounded natural arithmetic and admitted only when the result fits uint256.
The frontend parser remains trusted; no solc-equivalence theorem is claimed.
The focused development campaign passed 96 A/B/C transactions across three
equivalent variants, 56 acceptance/rejection controls and 16 semantic mutants
with positive controls and minimal witnesses. The numeric parent `b0fa7b0e2`
subsequently passed all 12 exact-head gates.


### Exact natural constant products (development)

Constant multiplication is admitted only for `int_const` operands that lower
to exact natural literals without preludes. Multiplication uses unbounded Lean
naturals and rejects results outside uint256. This adds no runtime wraparound
or floating-point approximation. Fractional operands and other rational
operations remain unsupported. The solc frontend is still trusted; no
Solidity-equivalence theorem is claimed. Focused validation at `bbc8fe0ad`
passed 96 A/B/C transactions across three equivalent variants, 60
acceptance/rejection controls (including an oversized intermediate), and a
product mutant detected after a positive control and reduced to a replayed
single-call deletion-minimal witness. Full exact-head gates remain pending.


### Inline constant array reads (development)

Direct unsigned fixed-array reads require each element to lower to an exact
natural literal without a prelude and to fit the array element width. The
index is lowered once; an out-of-bounds access panics with code 0x32 before
value selection. This slice materializes no memory array, so the array cannot
escape or participate in observable memory operations. Nonconstant elements,
guarded initializers and unsupported types reject rather than choosing an
evaluation order for their effects. Focused validation at `674cd89cd` passed
96 A/B/C transactions across three generated variants and 67 acceptance/rejection
controls. Element, selection and bounds mutants each passed an unmodified
positive control, diverged and were reduced to replayed deletion-minimal
witnesses; the bound witness retains `change(7)` followed by `fail()`, exercising
the index-eight panic. Full exact-head release gates remain pending; this is
not a Solidity semantics proof.


### Unsigned modulo (development)

Typed unsigned modulo lowers to the existing Denote/EVM remainder arm with
an explicit zero-divisor arithmetic panic (0x12), preserving operand preludes
and bindings. This differs from the raw EVM MOD zero-divisor result, which
must not replace Solidity's panic. Narrow unsigned operands use their
canonical values; signed and general constant-expression modulo remain
unsupported. Quotient-identity variants transform the defined-value arithmetic
and retain the zero-divisor probe verbatim. Expanding that probe to a quotient
produced identical panic bytes but different actual EVM storage reads under
solc optimization, so it is not an equivalent variant for this instrument.
The strict touched-slot comparison remains enabled. The fixture additionally
checks the reachable-state invariant `value <= 15` before the original
zero-divisor probe, preserving an actual storage read across global solc
optimization of each variant. This strengthens the fixture; the original
zero-divisor assertion and all observation comparisons remain intact. The coverage arm has a reflexive semantics lemma;
differential and mutation validation remains pending.

Modulo quotation corruption is tested as an exact model-integrity rejection
after a successful unmodified A/B/C control: it cannot produce an executable
model because the importer compares the reified model with the original.
Generic compilation failures do not count. Value and zero-guard mutations
remain runtime differential tests requiring replayed minimal witnesses.


### ABI array length (development, unvalidated)

The candidate lowering reuses the existing schema and memory materialization.
Calldata accesses invoke the lazy static-array header with the schema-derived
element stride. Correct validation and revert ordering for length-only accesses
remain to be established against pinned solc; no new verified support or
Solidity-equivalence theorem is claimed. Both memory and calldata fixtures
retain all existing controls and add length probes and semantic mutations.

### Default scalar local initialization (development)

The importer lowers Solidity default locals of supported unsigned integer,
address, bool and bytes32 types to zero in a fresh model local. This uses the
existing local-binding semantics and does not add an oracle or proof axiom.
Uninitialized memory/storage references and unsupported scalar types reject
at the declaration. Differential fixtures, explicit-initializer variants and
a nonzero-default mutation are added; validation remains pending.

### Scalar local writes (development)

Assignment and deletion of materialized scalar locals use the existing
`assignVar` semantics, preserving declaration identities and conversions.
The RHS prelude executes before assignment; deleting assigns zero. Parameter
expressions and aggregate/reference targets are not treated as writable locals.
No new oracle or axiom is introduced. Focused differential validation is pending.

### Invariant scalar loops (development)

A Solidity loop is lowered to existing `forEach` only with a zero uint256
counter, strict counter < bound condition and unit increment. Structural
analysis traverses all nested steps and rejects writes to the counter or
source local bound. Since iteration i satisfies i < bound <= 2^256-1, the
post-body increment is representable. Supported bodies cannot modify
parameters indirectly. Array-length hoisting, break and continue remain
outside this rule. Native differential and proof checks are still pending.

### ABI array-length loops (development)

Hoisting is admitted only for a schema-resolved ABI array and a body whose
recursive statement whitelist excludes memory writes and external calls. The
length decoder still executes at the first condition even for zero iterations.
This relies on preservation of the decoded header and calldata; memory-frame
proofs and native differential validation remain pending. No new oracle or
axiom is introduced. Future memory/call support must preserve this check.

### Development helper-loop lowering

The helper-loop draft shares existing bounded-loop validation and ABI memory-frame requirements. Its nonreturning body dispatcher rejects helper-loop returns instead of substituting root-return semantics. Helper results continue through the existing scalar inlining mechanism. No new oracle or trusted semantics arm is introduced. Native differential, rejection and mutation validation remains pending.

### Development mapping-struct member writes

This draft uses the existing pinned-solc storage layout and existing Denote/compiled `setStructMember`/`setStructMember2` semantics. Unsigned members must be present in the resolved layout; opaque members and key preludes at assignment are rejected. Alias keys are frozen at declaration to preserve storage-pointer identity. The alias issue is currently a source-audit concern awaiting runtime reproduction; tests, mutation witnesses and full release validation are pending.

### Development internal helper expression effects

The helper continuation delegates expression statements to the same exact assignment/delete/require lowering as root entry points. It introduces no new Denote instruction, oracle or trusted semantics arm. Helper scope restoration and scalar-result continuation remain unchanged. The draft fixture, generated variants, rejection controls and effect-drop mutation still require native and full release validation.

Stateful helper calls in ordinary binary operands or call arguments are not assigned an unverified Solidity evaluation order. A declaration-based source check precisely rejects those contexts; pure/view calls retain their existing behavior. The new guards and short-circuit write fixture are not yet kernel or runtime validated. The prior tuple-return require-helper audit establishes only its own pinned fixture's observation order.


### Development mapping fixed arrays

The importer uses pinned solc's resolved layout base/length/rounded footprint and
the existing masked mapping-struct instructions. Element i uses word
i / floor(256/width) and bit offset (i % floor(256/width))*width. This introduces
no new Denote semantics or oracle. Readonly memory copies materialize element
values at declaration; descriptors are restored at helper/block/loop scope
boundaries and reset between entry points. Unsupported memory uses and write
operand effects reject precisely. Preliminary recorded-hash A/B/C tests passed;
new-head focused variants, controls, mutation detections and full release gates
remain outstanding. No whole-contract or solc-Yul equivalence proof is claimed.

A separate fixed-array key/index helper audit on `2a448958` observed identical
stamp/order, revert bytes and rollback across32transactions on the pinned
A/B/C routes. This is fixture-scoped differential evidence, not a proof about
all key/index expressions or other solc settings. Existing rejection controls
and the full release gates remain required.


### Development fixed-array assignment order

The candidate lowering evaluates and captures RHS values before evaluating
mapped fixed-array key/index preludes and before bounds checks. This relies on
the pinned solc 0.8.34 via-IR profile; the retained A-only order fixture observed
RHS/key/index stamp `312`, exact RHS error priority and rollback. The fixture
is not a universal compiler-order proof. Dedicated A/B/C variants, mutation
witnesses and full release gates are pending. Existing unsupported-expression
and storage-layout checks remain applicable; external effects/calls are not
admitted by this change. No Denote semantics arm is added: capture, control
flow, panics and masked storage writes use the existing model semantics.


### Development discarded helper expression statements

Resolved internal/private scalar-result calls reuse the existing inliner and its
scope, recursion, argument-order and reference guards. The result is materialized
before being discarded; every prelude instruction, storage read, event and revert
remains observable. No new Denote semantics, oracle or ECM is introduced. This
statement rule does not model CREATE2 or replace deployment effects. Differential
fixtures, generated variants, near-miss rejections and the registered effect-drop
mutation remain pending native validation; no whole-contract equivalence is claimed.

Helper-result continuations also reuse the exact root `emit` lowering, keeping events
before the continuation and rollback intact. The fixture retains helper events;
a separate event-drop runtime mutation and anonymous/dynamic event rejection
controls are registered. Native validation remains pending.

### Development encoded-byte-local descriptors

The importer reuses existing ABI encoding, memory-copy and real Keccak paths.
An initialized bytes local records a declaration-id payload pointer/length after
evaluating its initializer once. Aliases reuse the descriptor. No new Denote
instruction or oracle is introduced. These descriptors do not expose a Solidity
length-header pointer, mutating byte operations, reference helper arguments or
CREATE2; those source forms remain rejected. Branch, loop, helper and root scopes
restore descriptor bindings together with existing reference environments.

The 64-transaction uncommitted draft fixture passed A/B/C; generated variants,
runtime mutants and located controls await final native/exact-head validation.
This does not establish general bytes memory equivalence or deployment semantics.

### Development named-helper result contexts

Named scalar helper results are lowered to fresh declaration-bound local slots
initialized before body effects. Existing scalar-write/branch/require/event
semantics are reused. Implicit fallthrough observes the result slot; explicit
returns terminate the helper path. Nested helper inlining restores the caller's
result context, return declaration id, lookup maps and scalar types. Existing
full-word single-terminal assembly keeps its direct expression lowering.

Assembly result assignments must resolve their target identifier through
`InlineAssembly.externalReferences` to the active helper return declaration id
(`!isOffset`, `!isSlot`, no suffix, `valueSize == 1`); shadowed local targets
with the same spelling reject. Reference-local declarations erase their name from
the Yul identifier map for their lexical scope. Assembly result assignments with
a continuation clean unsigned/address widths and normalize booleans before
Solidity reads. Yul reads of narrow named results are rejected rather than
substituting cleaned bits for raw assembly bits. No new Denote arm, axiom or Yul
builtin is introduced; code deployment and general raw memory remain unsupported.
Expanded type/scope/shadowing cases, runtime and guard mutants, generated
variants, located controls, exact-head release gates and the pilot check remain
pending.

### Development numeric Yul expressions

Untyped decimal and hexadecimal Yul numeric literals are parsed without rounding
or word truncation; out-of-range values reject. Two-argument Yul `add` lowers to
the existing wrapping word addition expression. Neither rule adds a Denote arm,
oracle, external effect or project axiom. General assembly, raw memory and
deployment remain unsupported. In particular, accepting literals does not make
CREATE2 executable or make an encoded-byte descriptor a Solidity object pointer.

Generated variants, two runtime mutation rules and eight located controls are
registered in the draft. Native A/B/C validation and all exact-head release gates
remain pending; no new semantic-equivalence or Midnight-unlock claim is made.

### Development struct fixed-size array members and root fixed-size array returns

Fixed-size inplace unsigned scalar array members inside mapping-backed structs
are expanded into synthetic `StructMember` entries only for slices that touch
the array member (`usedStructFixedArrays`), preserving existing `opaqueMembers`
reporting and layout declarations for slices that only access scalar struct
fields. Element reads and writes reuse the existing `structMember` /
`structMember2` / `setStructMember` / `setStructMember2` Denote and compiler
arms with explicit `Panic(0x32)` bounds guards; whole-struct `delete` and
whole-array `delete` remain rejected. Unnamed root fixed-size scalar array
returns (`T[L] memory`) lower to `L` static ABI return words (`returnValues`)
from either an inline array literal or a local fixed-size array snapshot
without introducing new Denote instructions or project axioms.

### Development `abi.encodeWithSelector`, `.selector` byte buffers, and extended Yul builtins

`lowerSelectorBytes` and `abi.encodeWithSelector` reuse the existing word-memory
allocation and byte-lane copy primitives (`AbiEncoding.staticWords`,
`AbiEncoding.packedBuffer`, `AbiEncoding.copyBytes`) and require a pure selector
receiver (`type(contract ...)`, `this`, literal, or local/parameter variable) so
storage-variable receivers cannot introduce optimizer-dependent `SLOAD` trace
differences. `lowerYul` extends the single-assignment inline assembly subset
with `sdiv`, `smod`, `exp`, `byte`, `signextend`, `slt`, `sgt`, `caller`,
`address`, `timestamp`, `number`, and `chainid`, pinning `Expr.smod`,
`Expr.byte`, and `Expr.signextend` in `Coverage.lean` by `rfl` without adding
project axioms or `native_decide`. External contract calls, `<addr>.code`, and
`abi.decode` remain explicitly rejected with source-located diagnostics.

### Development `string` and `bytes` storage variables (`encoding == "bytes"`)

Top-level `string` and `bytes` storage variables (`layout.encoding == "bytes"`,
`numberOfBytes == 32`) reuse the existing `Expr.storageArrayElement` and
`Stmt.setStorageArrayElement` AST constructors on scalar `FieldType.uint256`
fields to represent computed-slot `sload`/`tload` and `sstore`/`tstore` at
`keccak256(abi.encode(uint256(slot))) + i` without adding new `Expr` or `Stmt`
constructors, project axioms, or `native_decide`. Both reads, writes, and
`delete` enforce `solc`'s `Panic(0x22)` storage-encoding invariant on the base
slot word (`(raw & 1) == ((raw & 255) / 2)` when `0 < (raw & 255) < 64`), clean
trailing bytes of the final word on long writes, and zero out stale long-storage
words when shrinking or transitioning from long (`>= 32` bytes) to short (`< 32`
bytes) encoding. Storage `bytes` indexing (`b[i]`), `.push` / `.pop`, and
storage-pointer locals remain rejected with located diagnostics.

### Physical memory migration carrier

`ContractState.byteMemory` and the pure operations in `PhysicalMemory` provide
byte-addressed memory with exact overlapping-write and outside-byte frame proofs.
Source and IR `mstore` and scalar-return paths now install the byte carrier and
its word projection together; canonical Denote and public call-aware scalar
returns use the same physical write. The runtime/IR relation includes byte-carrier
equality; the generic core and terminal continuation proofs kernel-check with
that stronger relation. Bounded source-head equations and explicit offset/fuel
equalities avoid reducing whole byte-backed states, without increased local
heartbeat or recursion budgets. The two fields are not automatically coherent
for arbitrary entry states: callers still need the explicit
`PhysicalMemory.Coherent` predicate where coherence is required. Event scratch
memory, ABI memory and richer call/copy paths still need their integration checks.
These proofs do not expand the importer support set, establish whole-contract
real-EVM equivalence, or discharge the full Contracts/release gates.

`PhysicalEventMemory` supplies bounded sequential physical-write equations,
exact continuation composition and a signature-store execution lemma for the
`__evt_ptr` code shape. Its source/IR memory relation compares the byte carrier
and every word observation; its frame lemmas preserve all non-memory fields.
Declared-event source execution now uses physical signature and unindexed
scratch writers. Their equations and complete non-memory frames kernel-check,
and the general canonical Denote/source statement agreement still checks with
its unchanged observation boundary (the canonical Denote is event-less). The
supported-scalar declared-event signature/unindexed/log source/IR bridge now
kernel-checks with its original support, scope and fuel hypotheses and exact
byte-carrier/runtime agreement. It does not admit dynamic event parameters or
extend Solidity admission.

The signature scratch readback lemmas prove byte-disjointness of distinct
32-byte cells under the existing scratch-size bound, including modular offset
wrap. Readback compares the byte carrier directly and derives word observations
from proved coherence after nonempty physical stores; it does not assume an
arbitrary initial word map was coherent. The signature segment now uses these
physical poststates. Unindexed stores and the final supported-scalar event
agreement also kernel-check; broader ABI, call/copy and whole-contract release
integration still require their own checks.


The physical-memory consumer check now covers the unchanged function initialization,
dispatch, contract, guarded contract and scalar-event theorem modules.
`ContractFeatureTest` retains its constructor/helper/event regression assertions
and no longer uses `native_decide` or a local recursion-depth increase. Small
closed checks use kernel decision proofs; opaque helper evaluations are split
into exact head equations and complete physical-world return witnesses. The
function-filter call equation requires the actual unique internal callee filter
and preserves all evaluation, failure, binding and world observations. These
focused kernel checks are not full Contracts or exact-head release validation;
ABI memory and calldata/returndata copy integration remain unfinished.


`PhysicalCopy` supplies exact selector-plus-ABI-data byte sources and a copy
opcode update that preserves the entire entry world at size zero, without a
coherence premise. Its nine universal byte/word/frame lemmas kernel-check and
audit to standard axioms only. Canonical Denote uses this update for calldata
and bounded whole-word returndata copies. A handwritten unaligned 17-byte
copy followed by a distant physical store exposes the legacy divergence on
real EVM return bytes and storage, shrinks to one call, and agrees across A/B/C
after correction on the same four-transaction case. This fixture retains an
unchecked low-level obligation; it is measuring evidence, not importer admission
or a sustained campaign. All three source copy paths, the unchanged general
canonical Denote/source agreement, shared IR state copy operations and both IR
interpreter execution paths now kernel-check. The IR observation-preservation
theorems retain their original scope. Complete runtime/byte/word copy relation
adapters now kernel-check, including arbitrary zero-extent entry states. The
nine source/IR/adapter audit sets contain only standard axioms. Downstream
singleton continuations remain under validation;
ABI/call integration and full Contracts/release gates remain unfinished.
Selector-adjacent `calldataload` now reads the complete selector/data window:
DynamicAbi and the compiler mirror use exact byte-splice arithmetic, and
canonical Denote delegates to DynamicAbi rather than maintaining another copy.
All four offsets 0–3 were measured divergent before correction; the same
seven-transaction case agrees across A/B/C after correction. The static/dynamic
ABI round-trip checks and actual Denote harness dependencies kernel-check.
General source execution, the entire IR interpreter, unchanged canonical
Denote/source statement agreement and function-body base proofs kernel-check
against this load change. Broader downstream and full-library release checks
remain outstanding. Two real Denote mutants for the load and copy rules are
detected after separate unmodified controls and reduced to one-call EVM
witnesses. This focused result does not establish the full mutation gate.


The historical `DenoteMemory` operation layer now reuses the shared core byte
carrier and operations, rather than redeclaring incompatible copies. Its
literal source-store bridge describes the complete physical poststate; the
legacy single-cell word-map helpers remain isolated layout calculations. The
module and worked example kernel-check, and all seventeen public theorem audits
use only standard axioms (or none). This check does not discharge full-library
ABI/call integration, importer admission or the release gates.


The physical-memory integration checkpoint builds the complete `Contracts` target,
including the repaired SimpleStorage poststates and the bounded StateBridge byte
lookup proofs. This is a dirty-worktree build, not an exact-head release gate.
The initial audit of the three public SimpleStorage endpoints exposed the legacy
`Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq` native-code
decision axiom. The witness source now uses `decide +kernel`, which checks the
computed result in the Lean kernel; its isolated audit has only standard axioms.
Identifier collectors are total and preserve the original ordered folds, and the
switch temporary search has proved termination, collision freedom for both names,
and first-free selection. The decimal length bound proves termination without
truncating the search. These changes preserve the concrete witness statements.
The subsequent complete `Contracts` rebuild and imported ten-theorem audit
confirm that the three SimpleStorage endpoints, both witness theorems, and five
name-collection/search lemmas have only standard axioms. This is scoped to the
dirty integration receipt, not an exact-head release gate or an audit of every
contract proof. The axiom inventory explicitly includes this witness even though
it is outside `Compiler/Proofs`.

`Compiler.SolidityImport.AbiPhysicalMemory` now also proves the actual reserve
prefix and packed-buffer sequence with complete physical-world poststates,
including the pointer store followed by clearing in their real order. Rounded
payload clearing preserves every physical byte outside the allocation. Both
oversized and wrapped allocation failures retain the exact panic `0x41` bytes.
The real allocation, copy, aligned-grid arithmetic, and legacy ABI executor
modules now build, and all 79 public theorem audits have only standard axioms.
The store equations retain complete physical worlds, including overlapping
windows. The old distinct-offset word frame was false for overlapping 32-byte
windows; its replacement states geometric disjointness and explicitly relates
the redundant word view to physical memory. Physical store poststates and
outside-byte frames remain unconditional. The allocator proves the coherence
required by the copy-byte projection without assuming it in the initial world.
The copy loop preserves its persistent buffer descriptors, exact byte prefix,
coherence, and every Denote field except memory carriers and local bindings.
The grid arithmetic was moved with unchanged definitions/proofs into
`AbiMemoryGrid`, which `AbiMemory` and `AbiPhysicalCopy` reuse. No importer check,
golden model, mutation expectation, or source admission was changed by this
proof migration. The current bounded full-tuple Smoke consumer also builds,
and all five public theorem audits use only standard axioms or none. General
byte-call agreement and exact-head release gates remain separate obligations.

`Verity.Core.Model.CodeData.Create2.create2AddressFromMemory` hashes the complete
initcode slice before placing its digest in the EIP-1014 address preimage.
The word-view helper requires the caller to establish correspondence with actual
physical bytes; it does not execute initcode, implement deployment effects or
justify admitting Solidity CREATE2. Its equation and the other CodeData proofs
are included explicitly in the generated axiom inventory. The preserved
EIP-1014 example-zero vector checks both offset zero and an unaligned offset.
`Create2PhysicalMemory` proves equality of every byte and the complete slice
with the physical carrier under explicit word/byte coherence, then equality
of the resulting address. The slice theorem covers arbitrary offsets and
lengths, including crossings of word boundaries. These are memory-projection
proofs, not assumptions about creation success, account collision or runtime
code installation; those deployment observations still need implementation.

`Create2Accounts` provides the separate account projection needed at an entered
creation boundary: nonce, runtime code and balance. Reservation increments the
creator nonce before testing target collision, initializes a free target nonce
to one, and preserves balances and code. Its frame includes every other
account; target equal to creator necessarily collides after the increment.
This is an account-reservation component, not a complete CREATE2 evaluator.
The explicit projection is carried in `ContractState.creationAccounts`, so
world snapshots retain it. `CreationWorld` supplies its setter and full-world
frame (erasing only this projection), together with storage-preservation
equations. The existing `codeSize` observation is not silently redefined;
the eventual opcode evaluator must keep it consistent with installed code.
Gas/entry guards, initcode execution, runtime installation, failures and caller
rollback still need their actual semantics and EVM differential checks before
source admission. Adding the field does not make the opcode executable in Denote.

`Create2Runtime` finalizes the account projection for value-zero creation by
constructors with no persistent state changes. Successful code installation
retains the reserved nonce; constructor failure or rejected code restores the
target snapshot while retaining the creator increment. It enforces the 24,576
byte runtime limit and the `0xef` restriction, and preserves actual constructor
revert bytes. Initcode execution and the code-deposit gas decision remain explicit
inputs, not computed EVM semantics or project axioms. Its account frame applies
to the creation boundary, not transaction gas fees. The source-only EVM controls
cover empty-code nonce collision, caller rollback, both size boundaries, `0xef`,
deposit OOG and a four-byte constructor revert. They are not an A/B/C validation
or justification for admitting CREATE2 in the importer.

`CreationCommit` commits this component into the complete canonical world.
Successful installation synchronizes the actual target runtime length with
`codeSize`, retaining all other accounts' size observations. Successful creation
and empty-data failure clear the previous returndata. The current word-returndata
adapter rejects nonempty constructor revert bytes with an explicit interpreter
error; it never pads or discards them. A full-world frame erases only account,
code-size and returndata observations. This adapter is not yet a Denote opcode
arm, and arbitrary constructor reverts require the exact byte-call interpreter.

`MidnightInitcode` executes the actual eleven-byte constructor prefix
`600b380380600b5f395ff3` through nine bounded instruction steps, reading the
opcodes from the complete initcode. Its stack arithmetic is modulo 2^256;
CODECOPY uses fresh physical callee memory and RETURN reads that memory.
Universal kernel proofs show that every byte of the returned runtime equals
the appended payload, including empty payloads and unaligned word boundaries.
The word bound follows from the 49,152-byte initcode cap. The component rejects
unsupported opcodes and stack underflow explicitly. Its metered runner computes
opcode charges and quadratic memory expansion before each instruction; real
EVM OOG is distinct from host fuel exhaustion or unsupported instructions.
RETURN expands a nonempty memory window when needed and leaves zero-size
windows unchanged. Universal sufficient/insufficient-gas proofs cover every
successfully costed execution; the actual prefix costs exactly
`21 + 3*w + (3*w + w*w/512)`, with `w = ceil(payload.size/32)`.
Eleven real EVM opcode traces check every charge and full installed runtime;
six additional transactions check exact prefix-OOG and code-deposit boundaries.
These are separate oracle controls, not full A/B/C validation. CREATE2 caller
entry, EIP-3860/hash/forwarding charges, code-deposit integration, arbitrary
constructors and Solidity admission remain outstanding.

`Create2Callee` connects actual metered Midnight prefix execution to runtime
validation and the 200-gas-per-byte code deposit. It computes the returned code,
deposit success and exact gas refund; rejected code, prefix OOG and deposit OOG
are exceptional child halts consuming all forwarded gas. Its entered-boundary
API reserves accounts before execution and skips execution on collision.
Account updates reuse `Create2Runtime.finish`; failures restore the target
snapshot while retaining the creator increment, and the frame preserves all
other accounts. No constructor-result or deposit-availability certificate is
supplied. Actual forwarded gas is still an input: caller static/depth/nonce/cap
checks, memory/hash/EIP-3860 charges and EIP-150 forwarding remain outside this
API. The canonical opcode/source lowering and complete A/B/C are unfinished.

`Create2NonceEntry` enforces the EIP-2681 creator-nonce limit before the
entered-boundary evaluator. Nonce 2^64-1 returns failure with unchanged
accounts and refunds all forwarded gas, even if the target would collide.
An impossible greater nonce projection fails explicitly. Four new EVM
transactions check the last legal increment, overflow, overflow before
collision and collision after resetting the nonce, with actual opcode gas
and memory traces and EIP-150 forwarded-gas measurements. Anvil's call tracer
records a synthetic zero-gas-used creation frame on nonce overflow; absence
of child opcode execution is established by the instruction trace instead.
This is only the nonce gate: static/depth/value/cap guards and caller gas
charges still need their canonical semantics. Eight other retained EVM child
traces agree with actual `Create2Callee` execution on address, nonce, code,
balance, returndata and child gas; no compiler C or full A/B/C is claimed.

`Create2Entry` computes value-zero CREATE2 caller preparation from an explicit
actual opcode-entry context (gas, root-zero frame depth, static flag) and physical
memory. Post-Shanghai costs include 32,000 base gas, eight gas per initcode word
(EIP-3860 plus CREATE2 hashing), and quadratic memory expansion. It enforces
static prohibition, the 49,152-byte cap, sufficient caller gas and depth below
1,024, then partitions remaining gas using EIP-150. A depth failure refunds
all forwarded gas without account reservation. Universal proofs establish
exact split, full child refund and total caller gas after child consumption.
Inputs above uint64 gas fail explicitly; the context has no invented defaults.
This component is not a canonical world field or complete opcode: address
hashing, warm-account updates, nonce/callee composition and source admission
remain separate. The depth convention/order were checked against Revm commit
`7e59936c87794d0bc1d1d2d18b754f5a76fc37aa`, pinned in Foundry v1.5.0 Cargo.lock.

The new caller-entry controls cover complete expanded physical memory bytes,
unaligned/cross-word offsets, zero length at a maximal uint256 offset, initcode
cap boundaries, caller OOG and static prohibition. The pinned Anvil instruction
trace can omit a newly expanded zero suffix after a child returns; trace-array
length is not used as the authoritative active memory size. Separate bare EVM
MSIZE controls confirm expansion, and the source controls return a complete
nonoverlapping MCOPY snapshot plus a last-word probe charging only three gas.
Nine actual Lean/EVM entry pairs compare all snapshot bytes and exact gas split.
These remain component checks, without compiler C or source admission.

`CreationStorage` adds the successful-creation reset of the distinct target's
parked persistent storage words (`contractSlot` and persistent typed channels).
It preserves plain caller words, other accounts, transient channels and the
existing globally shared array metadata. Its complete frame changes only the
storage-word carrier; its commit composes this reset with `CreationCommit`,
retaining exact nonce/code-size/returndata updates. Failures preserve all old
storage. Four actual pinned-Revm controls seed a nonce-zero, code-empty target
with two nonzero slots and seven wei: creation clears both slots and preserves
balance, rejection restores both slots, caller revert restores nonce/storage,
and retry succeeds. This synthetic storage-only state exercises the pinned
Revm behavior; it is not a claim of Geth collision-policy equivalence.

`Create2Access` records target warming after successful caller preparation and
legal creator nonce, before target collision or constructor execution. Failed
constructors and collisions retain that access; caller rollback must restore
the previous set. Static/cap/OOG/depth/nonce gates do not warm the target. Five
source-EVM controls measure EXTCODESIZE charges (100 warm, 2600 cold), including
caller rollback and nonce overflow. These access and storage components are
not yet the composed canonical CREATE2 opcode or source admission.

`Create2Operation` composes these helpers into an executable value-zero
Midnight CREATE2 operation at an **explicit opcode boundary**. Its required
frame contains the canonical world, actual gas/depth/static context and the
transaction access set. Gas stays outside the rollbackable world. The operation
prepares physical caller memory, checks nonce overflow before hashing, computes
both EIP-1014 hashes from the complete actual byte slice, warms the target before
collision/constructor execution, evaluates the exact recognized constructor and
code deposit, commits account/code-size/storage effects and refunds remaining
child gas. Its creator is the world's actual `thisAddress`; self-target
reservation necessarily collides. An entered unsupported constructor returns
an interpreter error, while collision/depth/nonce failure skips constructor
recognition. Recognition checks equality of the **entire** code string against
the prefix plus the extracted payload, rather than accepting a certificate.

The same-caller snapshot helper restores the world and warm set while retaining
current gas. It does not execute the surrounding caller instructions or prove
their gas accounting. Twelve public kernel-audited lemmas establish recognition,
entry gates, self-collision, account frames and snapshot behavior. These facts are now exposed through explicit creation-boundary companions in
`SourceSemantics`, `DenoteState` and `IRState`; complete metered caller execution
and generic dispatcher/native-backend agreement remain obligations.
No transaction gas is guessed as gas at a later CREATE2 opcode; no source
function is admitted on the strength of this boundary operation.

New pinned-Revm controls seed different target addresses with seven wei and
two nonzero persistent slots, and retain complete physical opcode memory and
gas traces. Eight composed Lean/EVM boundary pairs match address, caller gas,
all memory bytes, creator/target nonce/code/balance, target code-size and slots,
caller-slot preservation, empty returndata and logs. A ninth entered reverting
constructor is explicitly rejected by the interpreter. Snapshot rollback is
calibrated for account/storage restoration while keeping the **opcode-boundary**
gas; this is not a proof of the surrounding caller's remaining gas at REVERT.
Warm-set behavior relies on the retained warm EVM controls and universal lemmas,
not on a newly measured warm read in these eight pairs. Ambient sender/block
fields are arbitrary and unchanged in this boundary test, rather than claimed
as observed chain state. Six executable semantic mutants (missing inner hash,
false collision success, missing storage reset, missing warming, warming on
nonce overflow and refunding consumed gas on rollback) are detected with replayed
single-fixture witnesses. These are component mutations, not the required
importer/Denote mutation gate for a future source lowering.


The canonical states carry `executionContext : Option ExecutionContext`.
`none` means unavailable gas/depth/static/access observations, and each explicit
creation boundary rejects it with `CREATE2 requires an actual opcode-entry
execution context`. It never supplies a non-static or gas default. The context
is outside the rollbackable world: same-caller rollback restores the saved world
and warm set while retaining current gas/depth/static mode. Both rollback
contexts must exist. Denote and Source companions execute the computed operation,
bind its address, preserve unrelated bindings and oracle index, and retain the
exhausted frame for exceptional entry. Creation uses no generic external-call
result or postworld oracle. `CreationAgreement` proves complete Source/Denote
state equality for these entry points and rollback.

`CreationIR.Frame` requires a canonical world plus a proof matching IR physical
memory, caller address, code-size observations, caller storage and returndata.
The projection preserves IR locals and carries the actual context; it does not
invent other-account data from an empty account map. Seven public proofs include
complete Source-state creation-boundary equality under the stated initial
world/context/binding equalities. These are companion APIs, not generic statement
arms, a native CREATE2 builtin, source lowering or whole-program gas proofs.
Unsupported constructors remain interpreter errors and Solidity CREATE2 remains
closed to admission pending those integrations and full A/B/C evidence.


`CreationCaller` executes a bounded local bytecode caller prefix up to, but not
including, CREATE2 using the pinned EVMYulLean EVM gas and instruction semantics.
Initial machine gas, PC, stack, calldata, code and environment are inputs; this
is not a projection of transaction gas into an unmetered source executor.
Jump destinations skip PUSH immediates with a total bounded scanner. The explicit
allowlist covers local arithmetic, stack, memory, control and calldata operations;
other instructions fail with bytecode-PC diagnostics. Fuel exhaustion is an
interpreter error, not an EVM revert. Checked instruction exceptions retain an
exhausted machine frame, while world rollback remains the caller's responsibility.
The derived context reads actual remaining gas/depth/permission. Its warm set
must be provided by an independently justified canonical projection.

EVMYulLean's materialized memory byte array may be shorter than its active memory
size. `physicalBytes` projects the entire active range, including its implicit
zero suffix; its size is kernel proved. Nine retained pinned-Revm source traces
calibrate root-entry-to-CREATE2 execution: exact boundary PC, gas, depth/static,
active words, every active memory byte and every stack item. The input gas is
observed at the first instruction. Unused account/header/address fields in this
allowlisted driver are arbitrary and are not claimed calibrated. This is still
not generic source/IR/native-Yul dispatch, compiled model equivalence, a complete
outer-call rollback executor or importer admission.

Executable caller tests load EVMYulLean's native FFI library for its zero-array
allocation (the Lean body is `Array.replicate`). Native allocation correctness
remains a runtime trust assumption, not established by the kernel proofs. The
library build cloned its upstream SHA2 and SHA3 support repositories, whose exact
commits and built library hashes are recorded in the local receipt. These caller
prefixes do not execute SHA/KECCAK instructions; the library's hash routines are
not evidence for those algorithms or translation validation.


`CreationBytecode` connects the executed caller prefix to computed Midnight
CREATE2 and returns the native next-instruction state. It requires a canonical
world and warm-set companion. It checks the native code-owner against the world
caller address and the entire executing code against that caller's canonical
account code, decodes the actual opcode, and reads value/offset/size/salt from
the actual stack. Nonzero value is unsupported interpretation, never a predicted
failed creation. Underflow/overflow, static prohibition and gas exhaustion retain
an exhausted exceptional frame. Executed prefix memory is synchronized into the
canonical world even when a prefix instruction exhausts gas.

The bridge installs actual physical caller memory, derives context from executed
machine gas/depth/static, and invokes `Create2Operation`. Continuation pops four
operands, pushes the computed address, increments PC and instruction count, and
installs computed gas/memory/access state and empty returndata. No supplied
opcode gas, predicted address, constructor receipt or postworld substitutes for
execution. Native other-account data is not claimed synchronized: creation uses
the mandatory canonical world. Further account-observing native instructions
need that world bridge and remain unsupported by the caller allowlist.

Eight saved real-EVM controls now calibrate execution from observed caller entry
through CREATE2 to the actual next instruction: all previous canonical world and
memory observations plus next PC, full native stack, active words, full native
memory and empty returndata. One constructor is precisely refused. The core
snapshot rollback account/storage comparison in these controls remains separate
from full outer caller execution and its eventual REVERT gas. Companion warm
inputs and unused native account/header fields are not newly chain calibrated.
This is not generic Source/Denote/IR statement dispatch, native Yul CREATE2,
importer lowering or whole-function A/B/C equivalence. Ten bridge regression
assertions exercise identity/opcode/value refusal, exceptional stack/static/gas
conditions, depth bypass and prefix-OOG memory retention; they are not additional
real-EVM campaigns or source-importer rejection tests.


`CreationExecution` executes the calibrated local caller/CREATE2 subset through
STOP, RETURN or REVERT, with one total instruction bound for prefix, creation
and continuation. It uses the existing checked native instruction and gas step,
synchronizes actual local memory after each step, and computes complete output
bytes from the halting machine. Unknown operations and fuel exhaustion remain
interpreter errors. Failed native/creation entry exhausts gas and restores the
canonical world/access snapshot. REVERT retains exact output and current gas,
restoring the canonical world/access snapshot. Six kernel-audited lemmas cover
local account framing, snapshot world/access/gas and exhausted failure.

Rollback here is a terminal result: the canonical snapshot includes its saved
memory, while the terminal native machine retains its last local observations.
It must not be reused as a resumed caller frame without an explicit enclosing
frame bridge. This handles root return/revert observations; it is not the
reentrant callback or caught-child rollback executor required by the roadmap.

Eight retained real-EVM root executions compare exact success/revert status,
full return/revert bytes, terminal remaining gas, every active native memory
byte, creator/target nonce/code/balance/code-size, seeded target slots, caller
slot and empty logs. The reverting source caller restores its original account
and storage state while preserving its measured gas. The ninth unsupported
constructor still produces a precise interpreter refusal. No caller-local
postworld oracle or supplied constructor receipt decides these observations.
These complete source-bytecode controls still do not execute an imported
CompilationModel function through Denote and compiled Verity: generic dispatcher,
source lowering and full A/B/C agreement remain necessary before admission.


Five executable `CreationExecution` semantic mutants are detected against the
same complete root EVM expectations and replayed on individual fixture witnesses:
keeping created state on rollback, refunding consumed gas, treating REVERT as
success, dropping output bytes and refunding gas after local steps. Private
executable mutants omit the original proofs; public proofs remain untouched and
compilation failure is never counted as detection. These component controls are
not the importer/Denote release mutation gate or stateful A/B/C shrinking.


Canonical `Stmt.create2 destination offset size salt` now represents computed
value-zero creation directly. `Denote.execStmt` evaluates its three expressions,
requires actual opcode-entry context, and computes account/storage/address/gas
through `Create2Operation`. Creation has no linked-call or ECM receipt: poisoned
generic external-call observations cannot supply its address or postworld.
The generic outcome type now distinguishes `interpretationError message` from
an EVM revert and preserves `exceptional state` for exhausted creation entry.
Statement lists and bounded loops propagate both outcomes. `DenoteResult` retains
an `interpretationError` field for function-level refusal; differential consumers
must treat a populated field as an interpreter failure, not a successful match
against an EVM revert. The ordinary function runner provides no invented context.

Five public equations audit actual statement dispatch and error/exception
propagation. Eight retained real-EVM boundary controls match the actual canonical
statement, including destination/local/oracle-index observations and precise
missing-context/unsupported-argument errors; one constructor remains refused.
The touched Denote module's five pre-existing `native_decide` smoke examples now
use kernel `decide` with unchanged propositions, and compile successfully.

The model descriptor exposes creation's operands, binding and existing `create2`
low-level mechanic. Compiler work emits a value-zero Yul create2 binding and adds
explicit operand/name/feature/trust traversal cases. This integration is still
unfinished at the generic IR/native boundary: compiler validation, Source statement
dispatch and universal Denote/Source agreement now cover the new statement and
outcome cases. Caller gas must be actual after argument preparation, and the native
Yul backend has no synchronized creation world yet.
Previous complete-library receipts are snapshots of earlier source states and
are not current gates. Solidity importer admission remains closed; no increase
in admitted Midnight coverage is claimed. Existing low-level guards are retained.


The CREATE2 compiler target now builds after explicit exhaustive-case updates.
`CreationLowering` kernel-audits the exact value-zero `create2` Yul binding and
state-read/write, persistent-write and external-execution classifications. ADT
operands are rejected, identifier scope checks inspect all operands and result
shadowing, and existing low-level creation guards remain in force. These AST
emission equations are not Source/IR or native-execution equivalence proofs.


The actual Source statement mirror now implements computed value-zero creation,
requires the same actual opcode-entry context as Denote, and preserves typed
interpretation errors and exceptional runtime states through statement lists and
bounded loops. Its 116 public theorem audits use only the allowed standard
axioms. SupportedSpec excludes creation from the unproved generic contract,
state/effect/call/foreign/low-level fragments while inspecting all creation
operands for helper and constructor raw-calldata dependencies. No theorem
hypothesis or observation was weakened to accommodate the new statement.
Creation in helper calls remains closed pending precise error propagation from
Option-valued helper evaluation; generic IR/native execution, whole-function
A/B/C and importer admission remain unverified.


The unchanged universal Denote/Source expression/statement/list/loop assertions
now cover typed interpretation refusal and exceptional-frame conversion. The
actual computed creation arm has its own public agreement equation; all 50
public agreement theorem audits remain standard-only. The existing plain-Source
revert projection still discards Denote payloads, so this is not a full-byte
revert theorem. Eight actual Source creation boundaries retain every expected
account/code/balance/address/storage/gas/physical-memory observation from the
saved EVM controls; a ninth constructor is precisely refused. Missing context
and unsupported argument evaluation remain interpretation errors, including at
the ordinary Source function boundary. No EVM transactions were replayed, and
these checks are not whole imported-function A/B/C release evidence.


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

Source-to-IR and Source-to-native correspondence now require `interpretationError = none` in addition to all previous success, return, storage and event comparisons. A refused interpretation cannot certify an ordinary EVM failure merely because those observable fields coincide. Function/constructor conversion proofs exclude refusal and exceptional outcomes using their existing statement-correspondence hypothesis; this does not enlarge that supported fragment. Full-byte transport and full CREATE2 function admission remain separate obligations.

Effectful IR statement stores now write the physical memory carrier: `mstore` updates all 32 bytes, and `mstore8` installs its low byte, with EVM-normalized offsets and coherent overlapping word reads. Argument evaluation remains right-to-left; these stores preserve the explicit creation-context schedule. Ordinary opcode gas is still supplied by authenticated native execution, not model fuel. The memory calibration instrument compares bounded generated store programs and equivalent variants against actual EVM transactions and DenoteMemory; it is primitive calibration, not a full imported Solidity/compiler equivalence certificate.

The prepared-creation calibration fixture now starts with empty physical memory and executes its constructor `mstore` in both effectful IR and the native bytecode prefix before authenticating CREATE2. The real-EVM checker compares created address and actual remaining caller gas immediately after CREATE2, plus successful return and empty storage/events for this fixture. Its interpreter launcher loads both the pinned external FFI library and the Lake-generated FFI module wrapper, recording artifact hashes. This remains a local component calibration; expression-helper diagnostic transport, arbitrary root transactions and whole-function compiler agreement are still separate obligations.

Typed source-expression outcome primitives distinguish values with full runtime state, ordinary revert, interpretation diagnostics and exceptional runtime state. Helper-body conversion restores caller locals while retaining the computed world, opcode context and call index. Argument-list sequencing threads computed states and stops on any terminal result. These are migration primitives, verified independently of the legacy evaluator; `SourceSemantics.evalExprWithHelpers` and its old consumers still use `Option`, so recursive expression-helper diagnostic transport is not yet certified. No helper-containing Solidity fragment gains admission from these primitives alone.

The staged recursive typed source evaluator now has a typed statement executor for assignment, scalar return/require, memory/transient/scalar stores, computed creation, conditionals, bounded loops and internal helper calls. Each expression consumer threads the computed runtime and preserves diagnostics/exceptional state; nested helper bodies use this typed executor recursively, with bounded resource fuel. Unsupported statements and unclassified primitive failures refuse interpretation. These modules are an explicit alternate instrument under migration, not the canonical whole-function Source/Denote compiler bridge. Compatibility proofs, all remaining statement forms, ordinary-failure classification, per-rule mutations and dispatcher integration are required before that boundary changes.

The staged typed executor also evaluates multi-value returns, immutable assignments and calldata/returndata copies. These consumers retain operand poststates and helper diagnostics. Out-of-bounds returndata copies require actual opcode context and produce an exceptional state with zero remaining gas; without context they refuse interpretation. Copy sources still use the existing whole-word returndata carrier, so arbitrary byte-length call receipts are not certified. Nine executable mutations cover the four initial recursive transport controls plus return order, immutable value, copy offsets and exceptional gas; they do not cover every statement/expression rule or establish the canonical Source/Denote bridge.

The staged typed statement instrument now handles declared scalar events and assigning internal helpers with multiple observed return words. Event operands are evaluated once before exact event/scratch-memory encoding. Assigning helpers enforce exact return arity and restore caller bindings and the caller's return marker while retaining computed world, execution context and oracle index. Public equations characterize multi-value success, refusal and exceptional transport. These changes do not migrate canonical Source dispatch, certify custom-error/revert bytes, or admit additional Solidity functions; generated coverage and canonical correspondence remain open.

`SourceTypedCompatibility` proves that successful helper-free primitives preserve the complete runtime, and characterizes typed primitive success in both directions. Its addition composition law threads the left operand's actual returned runtime into the right; resolved `require`/scalar-return laws agree with existing Source execution for normalized successful values. These are explicit migration steps, not a theorem covering all recursive expressions/statements or a canonical dispatcher replacement. Refusals remain distinct from ordinary reverts throughout.

The typed compatibility layer now characterizes successful argument-list execution by a recursive trace in both directions. Every trace step records the actual operand poststate, and the trace proves argument/return cardinality and composes invariants when every successful operand preserves them. A consumer law connects the trace to the actual typed `mstore`. Successful statement-list invariant preservation similarly composes per-statement obligations. These conditional composition laws do not supply those obligations for every entry point, prove rollback of failed frames, or complete recursive Source/Denote/compiler equivalence. Exceptional/refused/reverting intermediate states are not certified by the successful-outcome invariant predicate.

The typed creation operand trace now connects the actual typed Source statement to `Denote.execCreation` at its computed operand poststate. The prepared-creation real-EVM calibration executes constructor memory stores independently in typed Source, Denote and effectful IR, using only opcode context from the executed native prefix. It checks created/caller nonces, created runtime code, returndata, active memory bytes and actual remaining gas against the native companion; real EVM still calibrates address/gas/status/empty storage/events. This remains component calibration with the existing native canonical-world obligations, not importer admission or a whole-function compiler certificate.

A fresh solc/EVM calibration exposes an unresolved typed Source helper-return memory mismatch: after `mstore(0,19)`, a scalar internal helper returning 7 causes the current typed Source evaluator to observe memory word 0 as 7, while solc's internal assignment/leave preserves 19. Source scalar return currently reuses external-return memory effects inside helpers. The preserved reproduction is `.lake/source-internal-return-memory-baseline-20261014` (solc input/output, EVM receipt and typed runtime output). Internal/external frame return semantics must be distinguished before canonical helper-memory correspondence or creation-in-helper admission is certified. Existing component receipts do not certify this case.

The staged typed executor now distinguishes internal and external frames explicitly. Internal scalar returns preserve the computed runtime without external ABI memory writes; helper callbacks always run in internal mode, including nested conditional/loop bodies. The preserved internal-return memory witness now observes 19 in typed Source, matching its real solc/EVM receipt, while permanent checks retain the helper's independent memory write at 96. This repairs the staged typed instrument; the legacy canonical `SourceSemantics` helper evaluator still needs migration. The earlier failing receipt remains evidence of the original defect, not a passing campaign.

Helper return markers are now scoped in the staged typed executor: expression helpers and discarded statement helpers start with a fresh return-word marker and restore the caller's marker on successful completion, while retaining all computed world/context/oracle effects. Permanent tests cover caller markers both absent and present; production mutation inventories retain the prior controls and add marker-leak faults. Generated direct/conditional/loop return variants also exercise helpers that deliberately overwrite caller scratch memory, so preserving the caller marker must never imply restoring a pre-call memory image. Canonical migration and compiled-model differential integration remain separate obligations.

The durable generated internal-return memory instrument compares real solc EVM calls with independently generated handwritten CompilationModels compiled by Verity, and runs the same programs through the staged typed Source executor. Direct, conditional and loop helper returns cover preserved scratch memory and deliberate helper overwrites, including uint256 boundary values. Fixed memory operations declare an explicit unchecked local obligation, as required by the existing compiler gate; no checked memory or whole-function proof is claimed. This is component calibration. The canonical Denote helper lane, Solidity importer admission, failure observations and sustained whole-Midnight campaign are not certified by its successful receipts.

The staged typed executor now distinguishes a global STOP from internal return-word completion. Expression outcomes carry a separate halt state; binding/argument evaluation and statement consumers propagate it without evaluating the caller continuation. A STOP clears the callee return marker and retains the actual world/context/oracle effects while restoring caller locals. This distinction is not yet integrated into canonical Source or Denote dispatch. The generated instrument additionally calibrates void-helper STOP against real solc and compiled Verity EVM execution, while requiring rejection of declared-value STOP helpers by the unchanged exhaustive-return gate. STOP variants intentionally have empty external return data; they are not semantically identical to the successful scalar-return variants.

Source revert-byte transport is undergoing migration: `StmtResult.revertWithData` and public/internal result payloads now retain explicit bytes, and typed expression consumers transport that arm separately from refusal and exceptional termination. Exact string/panic/scalar custom-error encoding reuses the existing Denote encoders and canonical keccak oracle. Correspondence proofs and mutation/differential campaigns for this migration are pending; previous full-Contracts receipts predate it. Returndata still has a whole-word carrier, so this change does not certify arbitrary byte-length external call receipts.

Physical Error(string) calibration now executes the actual mixed literal/hex compiler stores through IR byte memory with sufficient fuel before capturing the actual REVERT slice. Store frame and byte-survival lemmas account for normalized offsets and overlapping unaligned header writes. Pure compiler encoding lemmas establish chunk length bounds, lossless concatenation of chunks, padded word length and uint256 word bounds. Kernel checks compare the complete observed payload to Denote.errorStringBytes for empty, UTF-8 and 31/32/33-byte messages; capture/size/read/absent-observation mutations are independently detected and replayed. These checks do not yet prove arbitrary-message byte equality, restore FunctionBody.Stmt correspondence, admit additional importer constructs or certify a whole-contract A/B/C campaign. No legacy word-only payload theorem is used to support this claim.

PhysicalAbiWordRecovery now proves arbitrary chunks of length at most32 recover byte-for-byte through valueWord/wordValue, with original bytes unchanged and zero padding explicit. Its stored_chunk_byte theorem connects this recovery to actual IR stores and later nonoverwriting normalized extents. The proofs reuse ByteMemoryInverse and have only standard propext/Quot.sound dependencies. Complete Error(string) payload layout, memory-address bounds and Source/IR function correspondence remain separate obligations.

PhysicalAbiChunkStores connects the compiler's actual zipIdx dataWrites to sequential chunk stores and proves every padded byte is read at its exact final offset. The theorem requires the complete physical extent to fit below or at Uint256.modulus; it does not silently identify wrapped offsets with unbounded host naturals. Initial memory may be arbitrary. Complete selector/offset/length header observation and the flattened complete payload relation remain to be connected.

PhysicalAbiChunkIndex proves the compiler chunk count and exact take/drop indexing, then connects every original byte and every trailing zero-padding byte to final physical memory after the actual chunk store sequence. The complete extent remains explicitly bounded by Uint256.modulus. This generalizes the chunk data region; complete Error(string) header/list equality and function correspondence are still unproved.

PhysicalErrorStringHeader proves all surviving selector bytes, all offset-word bytes and all length-word bytes after the actual overlapping header stores. With explicit nonwrapping data extent, data writes preserve every header byte; full_* laws connect those observations to the complete compiler writes list. These laws observe normalized valueWord length encoding. Agreement with the unbounded Source wordBytes encoder requires the relevant value bounds and remains to be assembled with the full payload list.

PhysicalErrorStringBytes now proves complete arbitrary-message equality to Denote.errorStringBytes, byte-by-byte and as the observed REVERT list, for every initial IR memory when the full data extent fits Uint256.modulus. execute_payload connects this exact observation to actual compiler-emitted stores followed by REVERT with enough fuel to execute all stores and the opcode. Length boundedness follows from the extent premise; no interpreter fuel failure is treated as an observed EVM payload. The public proofs audit only standard propext/Classical.choice/Quot.sound. This closes the component Error(string) encoding obligation; FunctionBody.Stmt correspondence, opcode-arm controls, complete Contracts and exact committed-head release gates remain pending.

FunctionBody.RequireBytes proves exact failed-core-require compilation and Source/IR payload correspondence with writes.length+extraFuel+4 fuel covering the nested stores and REVERT. A separate failed_require_ir_bytes law allows arbitrary unexecuted continuations. Permanent kernel checks retain nonempty UTF-8 bytes before a STOP continuation and demonstrate that the historical outer-list fuel budget exhausts without a captured REVERT. These new laws do not repair the legacy FunctionBody.Stmt list-wide correctness theorems; their fuel budgets and payload relations still require migration.

The exact failed-require proof now accepts any fuel budget at least writes.length+4 and proves the existing whole-body sizeOf fuel covers that minimum, including all nested payload statements. failed_require_ir_bytes_sizeOf preserves exact bytes with arbitrary unexecuted continuation. The remaining list-wide proofs must provide message-address bounds and replace their historical outer-list length budgets; no bound or success classification is inferred from fuel exhaustion.

RequirePayloadBounds introduces an explicit occurrence witness for require messages through canonical Stmt.childLists, including every nested statement form exposed by that traversal. requirePayloadsFit supplies the address extent of each such message, with checked tail/child/here projections. The terminal sizeOf proof now threads this premise and uses exact failed-require bytes. FunctionBody.Stmt still fails its two historical length-only core-list cases; no complete-module or function certificate is claimed from the absence of other diagnostics. Function consumers still need to carry the new bound.

FunctionBody.Stmt now builds with exact revertWithData byte relations. Sequential core-list correspondence requires explicit requirePayloadsFit and an extra-fuel reserve at least requireFuelReserve; the default theorem executes with that minimal reserve instead of the unsound outer-list-only budget. Tail induction preserves the reserve bound, and terminal lists use proven sufficient sizeOf fuel with recursive message bounds. Public result converters retain observed revert bytes. Function-level consumers have not yet been migrated, and the public Source/IR result relation still requires byte-observation strengthening; this module build is not complete Contracts or an exact-head release gate.

The public sourceResultMatchesIRResult now compares ir.revertData to none on success and some source.revertData on failure. Both statement relations require observed some[] for a payloadless EVM revert; absent observations cannot pass as empty. Generic step relations carry the same exact empty/nonempty requirement, and compiledStmtStep_require retains actual Error(string) bytes with an explicit address bound and structural fuel slack. execIRFunctionFuel preserves the actual physical revert observation, restoring adequacy with the canonical runner. Function-level body consumers and dependency builds remain under migration; no complete Contracts certificate is claimed.

Physical copy/revert bridge (2026-10-14): PhysicalCopyRevert proves each actual copied byte and the complete captured slice from arbitrary initial physical memory, including zero extent. Its returndata specialization observes the existing normalized whole-word byte source. It does not certify opcode execution fuel, exceptional-halt classification, equality to unbounded Source wordBytes, or arbitrary external-byte transport. Those require separate bounded-buffer/extent and execution correspondence proofs; full Contracts remains unverified.

Returndata bubbling proof (2026-10-14): PhysicalReturndataBytes.buffer_encoding/captured_buffer bridge the existing whole-word physical source to Denote.wordBytes under explicit word bounds. PhysicalReturndataExecution.execute/execute_payload run the actual let/returndatacopy/revert block with fuel extra+6, explicit buffer extent below uint256 modulus and word bounds; initial memory is arbitrary. A fuel extra+5 attempt exposed exhaustion before REVERT and is not certified. Generic induction consumers still need truthful premises and exceptional-halt handling; this component does not admit raw arbitrary-byte external returndata or certify the whole contract.

Returndata word-bound removal (2026-10-14): PhysicalAbiWordBytes.byte_encoding_unbounded proves exact ABI byte extraction invariant under reduction modulo 2^256 for every Nat word, using modulus factorization and modular division. PhysicalReturndataBytes.buffer_encoding_unbounded/captured_buffer_unbounded and PhysicalReturndataExecution.execute_payload_unbounded consequently require no word-value bound; earlier bounded interfaces remain valid corollaries. The opcode buffer-length bound remains explicit, as returndatasize normalizes that length. This supersedes the prior suggestion that unbounded word values necessarily differ in their observed ABI bytes; no carrier, assertion or golden was changed. Generic exceptional and whole-function consumers remain unverified.

IR REVERT boundary mutation controls (2026-10-14): IRRevertBoundaryChecks independently executes the opcode and the public IR result converter on nonempty, offset/expansion, observed-empty and zero-fuel cases. check_ir_revert_boundary_mutations copies the actual total mutually recursive opcode executors and public converter with frozen source/olean identities, changes exactly one production occurrence, then requires unchanged fixtures to fail and exact numeric observations to differ from baseline and replay identically. Controls target missing capture, ignored offset and erased public bytes; integrated into solidity_import_mutations. These component controls are not full imported A/B/C or exceptional-halt certification.

Generic returndata correspondence (2026-10-14): GenericInduction.ReturndataBytes links actual CompilationModel.compileStmt output, canonical SourceSemantics.execStmt and actual execIRStmts to stmtStepMatchesIRExec with exact explicit bytes. compiled_revertReturndata_exact_bytes uses the existing runtime alignment, existing structural slack and an explicit returndata extent below uint256 modulus; word values and initial memory are unrestricted. The old CompiledStmtStep package supplies no buffer-extent premise, so this checked theorem is not a certificate for its unrestricted legacy bubbling claim. Generic interface migration, exceptional-copy classification and exact custom-error payload obligations remain open.

Legacy payload/guard physical migration (2026-10-14): ErrorStringPayloadIR execution now uses actual normalized byte-memory stores, including pointer-relative writes; its old pure applyWrites facts are retained only as mathematical facts and are not physical execution certificates. The full Error(string) theorem retains selector/offset/length word assertions and additionally exact captured bytes, with explicit nonwrapping extent. PhysicalErrorStringWords proves the three actual overlapping word observations and memory coherence. CustomErrorPayloadIR REVERT execution retains actual computed capture (or absent observation on fuel/evaluation failure); its RevertsAlways facts classify only control, never certify payloads. NonReentrantGuardIR distinguishes the old minimum-budget exhaustion from actual empty REVERT capture; corresponding SpliceSimulation guard conclusions carry that exact observation. Generic custom-error payload and function-wide obligations remain open.

Custom-error scalar physical bridge (2026-10-14): PhysicalCustomErrorScalarBytes proves selector masking preserves exactly the first four ABI hash bytes, the following unaligned argument store preserves those bytes and recovers all32 scalar bytes, and sufficient literal-tail execution captures the complete4/36byte payload from arbitrary initial memory. No unbounded word-value restriction or hypothetical golden memory is used. SourceCustomErrorBytes.evaluated_payload derives actual Source bytes from evaluated arguments, unique runtime error declaration, arity/canonical scalar checks and supported type names. PhysicalSignatureHash now proves actual chunk stores recover every Source signature word including padding and preserve the exact Keccak input at arbitrary nonwrapping base addresses. This uses the actual in-tree hash computation, without an assumed hash-oracle equality. PhysicalSignatureExecution additionally proves execution of the compiler-shaped indexed mstore sequence to those physical stores and of the actual keccak256 let statement to the computed Source hash, under the observed pointer binding. The composed segment includes the actual free-pointer load, all stores and hash, with adequate fuel and a nonwrapping extent on the pointer read from memory; compile_zero_shape connects this segment and the unchanged remaining suffix to actual zero-argument revertWithCustomError output. PhysicalCustomErrorExecution now proves actual selector extraction, selector store, tail initialization, REVERT operands and complete zero-argument compiled block execution with sufficient fuel, and exact agreement with actual Source bytes under unique runtime declaration lookup. Zero-fuel execution is not used as a payload certificate. PhysicalCustomErrorScalarExecution now proves the actual scalar suffix and full compiled block capture all36bytes, including unaligned argument-store preservation of the selector, and joins actual Source evaluation/declaration/canonical checks to those bytes. Its argument evaluation premise is at the real post-prefix state; CustomErrorScalarEncoding proves the actual canonical encodings for every currently supported Source scalar type (uint256/uint8/uint16/valid uintN/address/bool/bytes32), derives argument evaluation through the physical prefix for scratch-independent atomic IR arguments, and joins their initial evaluation directly to the complete compiled/Source36byte certificate. CustomErrorExpressionFrame extends frame simulation recursively to nested operations/storage/environment/calldata expressions whose calls do not read memory via mload/keccak256 and whose variables avoid the scratch bindings; the actual prefix preserves its full visible-context Frame. Its compiled_recursive_source_bytes derives the complete scalar payload from initial expression evaluation. GenericInduction.CustomErrorBytes connects actual compileStmt(revertError) and canonical Source execution to the exact generic byte relation for zero-argument errors, retaining explicit compiler/runtime declaration lookup and extent obligations. GenericInduction.CustomErrorBytes additionally connects actual scalar compileStmt/revertError, compiled argument list and recursive expression/Source36byte correspondence. Its requireError failure rule carries the captured payload through the actual if with two additional fuel stages; compile_requireError_from_revertError checks the real conditional compiler shape, and the zero-error failure theorem joins both actual declaration lookups, Source condition and IR fail condition. The scalar require failure theorem composes actual scalar payload execution with the actual conditional compiler shape and failure execution, retaining initial argument evaluation, recursive scratch frame, canonicality, both lookups and the extra two fuel stages. The old coarse ErrorRevert/TypedRevertStep consumers have been migrated: exact pointwise helper-aware failure and success laws preserve the existing byte relation; zero-error typed admission uses CompiledErrorStepWithin with explicit CustomErrorDomain (actual declarations and per-error pointer extents) and a minimum fuel budget. Scalar/conditional typed consumers use actual Source/IR byte laws. These are not blanket CompiledStmtStepWithHelpers instances for arbitrary runtime declarations or exhausted fuel. Whole-function/list preservation and admission of that domain remain open, along with scalar/conditional domain instances. The complete compiler pointer/signature/hash/selector/encoded-argument prefix is linked to the computed Source payload for the supported scratch-independent scalar expressions above. Memory-dependent arguments and signed/bytesN Source support remain unfinished. The pointwise exact ErrorRevert and TypedRevertStep laws do not yet establish whole-function/list domain preservation or certify full Contracts.

Source declaration invariant (2026-10-14): SourceErrorDeclarations proves that every carried result of actual canonical and helper-aware statement/list execution preserves runtime.errors, including both bounded-loop executors, early return/stop, internal-helper callers and exceptional creation. function_entry_declarations instantiates the actual errors:=spec.errors body-entry assignment. CustomErrorDomain.after_helper_continuation derives declaration alignment from real execution; its physical extent premise still needs separate IR preservation. These laws do not certify full-function Source/IR equivalence, memory-dependent custom-error arguments or fresh Contracts/release gates.


IR physical coherence and error-pointer frames (2026-10-14):
`IRMemoryCoherence.executors` proves both actual fuel-indexed statement/list
executors preserve the equality of the legacy word observation and physical
byte-memory word projection, for every statement, loop and exit, including
fuel exhaustion. The premise is initial coherence, not an arbitrary legacy
word map. `CustomErrorMemoryFrame` proves physical disjoint stores/copies
preserve the actual error-pointer extent domain under that premise; zero-byte
copies are the identity without coherence or disjointness requirements.
Writing the pointer itself requires every actual normalized new-pointer
signature extent to fit. These laws do not yet establish the domain at every
error point of an imported whole function; allocation and argument invariants
and precise fuel must still be threaded through generic list/function proofs.

`CustomErrorContinuation.prefix_then_error` composes actual helper-aware
Source and IR prefix executions with a `CompiledErrorStepWithin` suffix.
Source declarations and IR coherence at the continuation are derived from
execution; legal extents use the prefix's explicit memory64 frame. IR suffix
fuel is the original list fuel minus the number of prefix statements, checked
against the admitted error step's minimum. This composition does not by itself
prove that arbitrary prefix IR was produced by the Source prefix compiler, nor
that arbitrary allocation preserves the pointer frame. Full compiler-list
admission and the concrete prefix frame obligations remain open.

`CustomErrorListCompilation.compiled_prefix_then_error` additionally derives
the identity of the actual `compileStmtList` output from a compiled Source
prefix and the domain-admitted error suffix. It uses the real compiler's
binder accumulation at the continuation scope, then composes exact execution
at the checked residual fuel. This removes an arbitrary-IR-prefix identity
from this composition; concrete prefix correspondence, pointer frames and
function-entry/dispatcher integration remain required for whole functions.

`CustomErrorPrefixFrame.compiled_framed_prefix_then_error` derives the pointer
frame from actual execution and per-opcode frame certificates. `let` and
assignment preserve every memory word; a literal-offset physical `mstore`
preserves the observed complete word when its EVM-normalized 32-byte write
is disjoint, under initial physical coherence. The list law propagates that
coherence via the actual executor at each continuation. It accepts additional
opcode certificates without excluding statement families by definition.
Allocation overlapping memory64 requires a new-pointer extent law instead;
full entry/dispatcher admission and other concrete prefix frames remain open.

`CustomErrorFunctionEntry` derives IR physical coherence from the real
`initialIRStateForTx` and a coherent initial world. Parameter binding preserves
memory and coherence; actual `genParamLoads` execution reaches that same
bound entry for the existing supported scalar decoder. The Source entry uses
`errors := spec.errors`; legal error extents are checked on the actual retained
world pointer. The loaded-body law transports exact IR execution through the
ABI loader, and `public_source_error` proves actual public helper-aware Source
rollback with the observed revert bytes. These are entry/projection bridges,
not full dispatcher equivalence: dynamic-parameter loading, concrete full-body
admission, prebinding in `execIRFunction` and dispatcher/result linkage remain
separate obligations. No initial pointer or memory contents are synthesized.

`CustomErrorFunctionResult.public_error_match` joins actual public Source
helper-function and actual `execIRFunction` failure observations using the
existing exact result relation: interpretation refusal absent, status/return,
all encoded storage slots restored, events restored and actual captured revert
bytes. IR execution is at `sizeOf compiled.body + 1` from the function's exact
argument-prebinding state; an exhausted/unclassified revert is not sufficient
without the captured-byte proof. Prebinding preserves memory/coherence.
This projection requires actual Source and IR body execution proofs; it does
not assume the supplied IRFunction was compiled from the Source FunctionSpec.
Connecting concrete body compilation/admission and dispatcher choice remains
necessary for an end-to-end imported-function theorem.

`CustomErrorFunctionResult.selected_contract_match` transports the exact function
result through the actual Source and IR dispatchers, with selector selection,
payment admission and raw parameter-count admission explicit. The transaction
update retains the real `initialIRStateForTx`; no new memory is introduced.
`CustomErrorCompilationOrigin.components` derives the actual ABI-prefixed body,
using `fn.bindingParams`, from successful `compileFunctionSpec` for any fork,
ADT table and internal-function table. Its metadata law derives selector,
payability and raw parameter count (`fn.params`). The compiled selected-contract
law derives IR admission guards from that compiler origin. It still requires
actual function-list selection and an exact body-result proof; guarded-function
compilation and the contract's compiled list must be connected separately.
These laws do not constitute full imported-contract equivalence or EVM evidence.

`CustomErrorDispatchCompilation` derives selector/payment/parameter metadata
through the actual transient reentrancy-guard injection, including arbitrary
forks, ADTs and internal tables. Its successful-mapM selection law retains
first-match order, even for duplicate selectors, and yields the selected
function's exact compiler receipt. `guarded_list_selected` joins that law to
actual Source lookup over `selectorFunctionPairs`. The list receipt is still
an explicit premise: extracting it from full `compileValidatedCore` success,
and proving the selected guarded body's exact observations, remain necessary.
No lock-free, no-internal-function or absent-special-entrypoint restriction is
introduced by these laws.

`CustomErrorContractCompilation.core_functions` extracts the actual guarded
external-function map from unrestricted successful `compileValidatedCore`.
`compiled_functions` carries this receipt through public input validation;
`compiled_selected` derives the selected IR function and its guarded compiler
origin from full compilation and actual Source selection. Internal functions,
special entrypoints, template helpers, ADTs, forks and locks are retained.
`compiled_contract_match` composes this with both real dispatchers, deriving IR
admission guards from compiler metadata. Its remaining obligation is exact
Source/IR semantics for the selected actual guarded compiled body; payment and
raw argument-count admission remain explicit. This is not a proof that every
imported body satisfies that obligation, nor a replacement for real-EVM tests.

`CustomErrorLoadedFunction.loaded_prebound_body` runs the actual scalar ABI
loader from exactly the argument fold used by `execIRFunction`; the transaction
calldata is preserved by that fold. `zero_error_function` derives concrete
zero-argument custom-error bytes from the actual physical payload executor,
then composes prebinding, loader and public rollback through the existing exact
result relation. It no longer requires an exact-body-execution oracle. It still
requires actual loader bindings, unique error declaration, legal retained-world
signature extent, and the explicit equality matching the executor's `sizeOf`
fuel. `compiled_zero_body` derives the ABI/payload body shape from real
`compileFunctionSpec` and declaration lookup for arbitrary fork/ADT/internal
table. This error-only path does not yet certify allocating prefixes, scalar
error arguments, guarded acquire/release, or dynamic-ABI functions. Deriving
structural fuel bounds and broader body admission remains necessary.

`CustomErrorFunctionFuel.zero_payload_fuel` proves a structural `sizeOf` bound
for the actual zero-error block, with arbitrary signature chunk-store count
and arbitrary loader prefix. `zero_payload_extra` derives the sufficient extra
fuel. `compiled_zero_error_function` therefore eliminates both manual body
shape and fuel-equality premises. `compiled_zero_error_contract` joins that
concrete body law with actual full compilation and both dispatchers, preserving
exact status, return, storage rollback, events and revert bytes. This selected
path requires no reentrancy lock; other contract entries remain unrestricted.
Real scalar ABI bindings, declaration lookup/uniqueness and nonwrapping retained
world memory extent remain explicit. Scalar conditional error paths, allocating
prefixes and guarded selected bodies still require their own admission laws;
this theorem does not claim whole-importer or real-EVM equivalence.

`CustomErrorFunctionFuel.scalar_payload_extra` derives executor fuel for the
actual one-scalar custom-error block at arbitrary signature length and loader
prefix. `CustomErrorScalarFunction.compiled_scalar_error_function` derives
actual function body shape from `compileFunctionSpec`, uses that structural
fuel, and joins real scalar error encoding/physical writes/captured payload to
prebinding, ABI loading and public Source/IR rollback. No exact-body-result
oracle or manual fuel equality is assumed. Actual Source argument evaluation,
canonical scalar validity, initial loaded/prebound IR evaluation and recursive
scratch-independence remain explicit. Scratch-dependent memory arguments,
broader signed/bytesN Source support, conditional/prefixed bodies and selected
guarded bodies are still open. Full compiler/dispatcher selection must be
composed separately; no whole-importer or real-EVM claim follows from this law.

`CustomErrorScalarContract.compiled_scalar_error_contract` composes the actual
full compiler and both dispatchers with the concrete scalar-error function
law. The selected entrypoint has no lock; other entries may remain guarded.
Its initial IR argument evaluation certificate is tied to the actual selected
guarded compilation receipt, not an arbitrary IR body. Source argument/type,
ABI binding and retained-world extent obligations remain explicit. Selected
guarded bodies, memory-dependent arguments and conditional/prefixed paths are
not certified by this theorem.

The prefix-frame, loop invariant, symbolic terminal-step and physical ABI
allocation/copy proofs now cover the canonical interpretationError and
exceptional outcomes explicitly. Their original assertions and postconditions
are unchanged: excluded exits follow from the existing false exit invariant;
general terminal/loop laws preserve exact refusal messages and exceptional
states. Neither outcome is coerced to an ordinary EVM revert.

`CustomErrorConditionalCompilation.require_from_revert` uses the actual
conditional compiler for arbitrary events, ADTs, fork and internal-function
table. `compiled_zero_body` derives the ABI-prefixed body from real
`compileFunctionSpec` success. `CustomErrorConditionalFunction.zero_conditional_extra`
derives sufficient `sizeOf` execution fuel for the actual if-wrapped payload;
`compiled_zero_failure` connects the helper-aware Source condition, actual
prebinding and scalar ABI loader to the physical four-byte custom-error payload
and public rollback. Condition compilation and both initial condition evaluations
remain explicit admission certificates; no whole-body execution oracle is assumed.
`CustomErrorConditionalContract.compiled_zero_failure_contract` joins actual
full compilation and both dispatchers for a selected unguarded failing conditional
zero-argument error entry. Other entries remain unrestricted. Scalar ABI binding,
declaration uniqueness and retained-world nonwrapping signature extent remain
necessary. Passing conditions, scalar conditional arguments, allocating prefixes,
guarded selected bodies and dynamic ABI functions require further admission laws.
This proves Source/IR observations for that path, not whole-importer or real-EVM
equivalence, and adds no Solidity importer admission.

`DenoteEquivalence.denote_eq_sourceSemantics` retains its original supported-function
boundary and equality. Its proof now uses the actual `spec.errors` field of the
initial Source runtime, matching the actual Denote and Source function entry.

The staged `IRCreationInterpreter` now transports `.revert data runtime` through
argument evaluation, statement lists, blocks and loops as a terminal outcome.
`invokeRevert` captures and returns the actual physical slice; its payload law
proves that the reported bytes equal `IRState.revertBytes`. `invokeReturndatacopy`
normalizes all EVM operands and copies exact bytes within the existing whole-word
returndata carrier. A bounds failure requires a supplied opcode context; it
produces an exceptional result with zero gas and unchanged memory/schedule.
Missing context and malformed arities produce explicit interpreter refusals.
The native CREATE2 boundary rejects a byteful argument-terminal outcome as it
already rejects other terminal argument effects.

These are staged execution components. Successful copy/REVERT gas, memory
expansion costs and the supplied context are not authenticated here. Arbitrary
raw returndata bytes beyond the current word buffer, canonical legacy IR
failure classification, actual full-function context metering and Solidity
creation/external-call importer admission remain open. The separate returndata
program calibration compares freshly executed real EVM transactions with typed
Source and effectful IR, including exceptional gas exhaustion, exact copied
bytes and semantically equivalent wrappers. It is primitive evidence, not
whole imported-function A/B/C or exact-head release validation. Seven semantic
mutations have independently successful permanent-fixture baselines and detected,
replayed divergences; compile/tool failures are never mutation kills.


Canonical returndata copy integration (2026-10-14): SourceSemantics ordinary,
event-aware and helper-aware copy arms and compiler-free Denote share
Verity.Core.Model.ReturndataCopy.run. Operands normalize modulo 2^256; valid
copies preserve the actual physical bytes. An out-of-bounds copy with actual
context preserves the world and exhausts opcode gas; missing context produces
an interpretation error, never an invented REVERT. DenoteAgreement proves
the adapter correspondence without restricting the state. Permanent executable
checks cover all four canonical consumers, operand normalization and refusal.
The primitive EVM instrument now observes these consumers alongside typed
Source and staged IR. Canonical IR result/dispatcher migration, legal retained
buffer extents, generic Storage correspondence, successful-opcode gas and
arbitrary byte-length returndata remain open; this adds no Solidity admission.


Canonical IR typed terminal integration (2026-10-15): IRInterpreter's expression,
value-list and ordinary/helper statement result carriers now retain exceptional
and interpretation-error outcomes through actual sequence/control/helper paths.
RETURNDATACOPY normalizes its operands, reports actual-context gas exhaustion or
precise missing-context refusal, and preserves the physical world frame. Internal
REVERT now retains the callee's captured memory state while restoring caller
variables. Public IR function results retain exception context/refusal metadata
separately from REVERT bytes, with storage/mapping/event rollback. Existing scope
and conservative-extension theorems compile with exhaustive typed terminal cases;
the unchanged physical-memory coherence theorem compiles using bounded explicit
branches under the default kernel budget. Permanent component laws verify terminal
suffixes, missing-context execution, function metadata/rollback and helper capture.
Fresh seed214 calibration passed 36 real-EVM transactions against the canonical
IR and Source/Denote consumers. All eleven canonical IR semantic mutants compiled,
were detected by the permanent runtime fixture, and produced independent minimal
expected/actual/replay witnesses; recorded source hashes match current inputs.
Direct permanent runtime checks passed. The four canonical compatibility/coherence
laws audited use only propext, Classical.choice and Quot.sound. This is component
evidence: global Source/IR relations, helper operand evaluation order, native
context authentication, legal retained-buffer extent and full contract
correspondence remain separate uncompleted obligations.
This extends canonical result transport, not CREATE2 Solidity admission or a
sustained imported-contract A/B/C certificate. Prior smoke success predates this
IR migration; it must not be promoted as validating these changed semantic inputs.


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

PublicResultBridge (development, 2026-10-15) relates actual Source bodies to
public results using the exact supplied context, oracle, cursor and declared
error table. It does not authenticate native frame inputs or expand ordinary
certification to exceptions/refusals. Function projections retain actual physical
revert bytes and distinguish exceptional context from interpreter refusal.
Physical Error(string) extent is a checked production function/import boundary,
including canonical nested bodies, rather than an unstated assumption about
arbitrary Lean Strings. Consumer integration, mutation coverage and full gates
for this boundary are not yet complete.


Constructor require-message validation now applies the same exact physical ABI
extent gate before all preserved pre-existing constructor checks. The body-only
constructor bridge is being migrated to consume successful production validation;
raw body compilation alone does not establish that arbitrary mathematical Strings
fit EVM addressing. Its result relation is unchanged. This migration and its
concrete callers are not yet validated, and no whole-contract success is claimed.


Payload guard mutation instruments (2026-10-15, campaigns pending): seven
actual-definition validator mutants exercise finite payload admission, canonical
deep-walk polarity and preservation of old function/constructor checks. Two
actual importer guard mutants deliberately over-reject finite messages; their
private importer modules must compile before source-located rejections and
minimal replays are scored. These instruments do not claim runtime testing of
astronomical strings at the word-address limit. Universal occurrence/extent
proofs cover that mathematical boundary; full gate/campaign success is separate.


Dispatcher rejection bytes (2026-10-15, integration pending): actual interpretIR
and interpretIRWithInternals now label unknown-selector, nonpayable-value and
short-argument rejections with observed `some []` REVERT data. These are the
explicit REVERT(0,0) guard/default paths emitted by CodegenCommon, not an
assumption that unobserved physical REVERT memory is empty. No payload is
fabricated for an arbitrary executed body REVERT; its existing optional capture
is unchanged. Generic and concrete dispatcher shape equations retain exact
payload comparison. Six quantified guard/rollback fixture laws now compile, together with Function,
DispatchGeneric, Dispatch, Contract and concrete ContractFeatureTest consumers.
An eight-law dispatcher audit and a ten-law current function/constructor/bounds
audit use only standard Lean axioms. Broader native context/gas and full Contracts
gates remain open.


Dispatcher mutation scope (2026-10-15, focused campaign passed): the new private-clone
runner changes each of the six actual dispatcher guard payload records
individually. It requires standalone elaboration before scoring rejection by
the unchanged quantified fixture laws, plus a separate minimal kernel-reduced
byte observation and identical replay. All six mutants compiled separately, failed the unchanged quantified assertions,
and changed independent minimal observations from some[] to none with identical
replays. Source and generated artifact hashes were independently verified. This is proof-side
mutation coverage, not real-EVM agreement or a full Contracts result.


Payload importer guard evidence (2026-10-15): both actual importer guard mutants
compiled privately and over-rejected finite Unicode/minimal messages with the
expected file:line:column diagnostic and no output olean. Unchanged controls
imported, and minimal replays matched. All recorded source and generated artifact
hashes were independently checked before later facade/proof refactors. These
receipts cover that frozen identity, not a later head or the global suite.

Bounded payload proof maintenance (2026-10-15): the exact physical Error(string)
byte theorem is decomposed into selector, offset, length, original-data and
padding lemmas; public contextual packaging and conditional lock-release proofs
reuse their existing semantic laws. The focused production rebuild now passes,
including Function and the scalar/conditional custom-error contracts. Shared
ABI/body/rollback composition and physical-signature/guard-shape lemmas remove
all outstanding proof-length violations without allowlist additions. Eighteen
focused laws use only standard Lean axioms. Fuel and splice proofs propagate
actual exceptional states and interpreter refusals unchanged; these outcomes
never become REVERT certificates. Full Contracts, required differential gates
and exact-head release validation remain outstanding.

Generated payload evidence (2026-10-15): 84 actual imported scalar program
variants completed 1,596 A/B/C cases without divergence, including UTF-8
message lengths 0, 6, 31, 32, 33, 63, 64 and 65 and custom errors with zero or
two arguments. An independent audit decoded the guard operands from source
calldata and checked all 621 guard-failure payloads against direct ABI encoding.
The combined runner nevertheless exited with a Python module-resolution error
before its first memory child; that receipt remains failed. After fixing only
the child launch environment, the six previously unexecuted manual memory
variants completed 72 stateful transactions without divergence or metamorphic
differences, with unchanged implementation identity during that phase. These
are separate, identity-specific instrument receipts; they do not certify the
current publication head or a sustained whole-Midnight campaign. No additional
Solidity construct is admitted by these observations.


Public Denote exception boundary (2026-10-15): `DenoteResult` now retains an
actual optional `ExecutionContext`. Public exceptional execution rolls back
storage/events and preserves the terminal carrier only when its opcode gas is
exhausted. Missing or nonzero-gas contexts produce explicit interpretation
refusals; they do not certify ordinary REVERT or invent an opcode context.
`DenoteAgreement.toSourceResult` preserves that carrier. The original universal
event-free `denoteFunction_eq` statement compiles unchanged, with explicit
projection case splits; its axiom audit and the projection lemma use only
`propext`, `Classical.choice` and `Quot.sound`.

The actual bounded-copy fixture executes and checks terminal gas/depth, rollback,
invalid-context refusals, contextless public entry and Source-result projection.
Five production-definition semantic mutants compile, fail those assertions and
produce distinct independent minimal witnesses with identical replays (projection
erasure, carrier erasure, nonzero gas accepted, missing context accepted and
rollback erased). Focused integration passes 1288 jobs with the unchanged warning
baseline3. These are dirty-tree component receipts, not exact-publication-head
or full Contracts gates. Public entry still does not synthesize opcode context;
whole-function native context/account/world integration and sustained Midnight
validation remain open. No new Solidity form is admitted by this repair.


Native creation-world observations: `Compiler.Proofs.IRGeneration.NativeCreationWorld`
exposes actual native account presence, current/original/transient slots, access
sets and raw logs, with local frame lemmas. `Agreement` remains a required proof
input; it is not established merely by constructing a source world. In
particular, default-valued account lookup does not prove account existence, and
account warmth does not prove storage-key warmth. The component fixture invokes
pinned `EVM.X` exceptional checks and mutations test each observation against
unchanged runtime assertions and minimal replays. Neither those tests nor the
frame lemmas certify source hashed-channel/event decoding, native world changes,
computed-creation synchronization or whole-function equivalence. CREATE2 source
admission and the sustained whole-Midnight campaign remain unfinished.


Native caller prechecks retain static SSTORE/TSTORE/LOG refusal and SSTORE's
2300gas stipend sentry after memory charging. The caller whitelist remains
closed to world-changing opcodes; the explicit helper gates are tested against
actual `EVM.X` and mutated independently. Source-world preservation and native
account synchronization remain separate obligations before any expansion.


Native storage frame laws refer directly to pinned State.sstore/State.tstore,
including explicit account presence for the update laws. They retain original
transaction storage and event-time logs; they do not identify source mapping
channels with flat native storage or prove complete checked-opcode/world
preservation. No extra axiom or source-admission assumption is introduced.


Native read-after-write and distinct-slot laws use actual Account.updateStorage/
updateTransientStorage and Std.TreeMap proofs, including zero-entry erasure.
NativeCreationWorldWrites reuses the shared proved native UInt256 TransCmp
instance in StateBridge. It does not assume source/native storage agreement or
extend the accepted opcode/source fragment.

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

The portable `native-midnight-source-caller` capture binds the actual pinned
Midnight library sources, exact solc binary/settings, generated ABI cases and
977-byte runtime. Its native fixture executes the real dispatcher/ABI prefix
and whole native continuation. Real-EVM calibration records status/return,
touched slots/events, traced creation memory/operands/gas, deployed code and
creator/target nonces. Captured-code and malformed-input mutants must fail
actual runtime assertions; compiler errors are not detections. Denote is still
related at an explicitly projected boundary, so these tests do not establish
the source ABI prefix or universal whole-function equivalence. The native/pure
hash equality guards remain pointwise; the capture does not assert universal
FFI correctness. No new importer admission or trusted axiom is introduced.

The portable source controls additionally cover target code/nonce collisions
and malformed dynamic Market calldata using the actual captured solc runtime.
The native collision control compares operation-boundary worlds and the source
custom revert, while Foundry independently observes committed root rollback.
The native revert result does not expose a final world, so Foundry rollback
observations are not a native-world rollback theorem. Malformed-input controls
compare exact empty revert bytes/gas and absence of writes/creation/events;
they do not establish general ABI validity or importer rejection diagnostics.
Generated malformed literals use bounded chunks without raising kernel limits.

The separate portable post-success rollback source capture authenticates the
real IdLib deployment followed by an event and caller revert. Foundry traces
must prove child success and the event before the terminal custom revert;
committed code/nonce/storage/event rollback is checked independently. Native
execution proves the same creation boundary and terminal gas/revert bytes, but
its revert API does not expose the final world. This instrument preserves that
limitation and does not infer a native-world rollback theorem. Existing source,
collision and malformed-ABI captures are retained as separate identities.


### Stateful external-account and caller initialization

`AccountsInput` parses mandatory exact decimal words/full code bytes and rejects
noncanonical values, uint64 nonce overflow, uint256 balance overflow, duplicates
and reserved caller/sender addresses. Its frame lemmas preserve persistent
storage, physical memory, events and unrelated account metadata. `CallerInput`
requires the actual model target, excludes senders, and synchronizes caller
account, code-size and scalar balance projections. These bounded proofs are
included in the generated axiom audit.

The Python bridge trusts an owned Anvil RPC node to install/read back supplied
external accounts and return historical deployment snapshots. The snapshot is
read at the successful receipt's block, checked against its block hash; it is
never observed after the tested calls. Each EVM route retains its own code.
Denote receives the source deployment snapshot, not a substituted Verity runtime.
Exact initial metadata is not a proof that arbitrary source/compiled self-code
introspection agrees. No gas, creation result, or executed postworld is accepted
through these inputs, and CREATE2 importer admission remains closed. Real-node
and compiled Lean semantic mutations exercise the parser, installation, reserved
addresses, leading-zero code and receipt-vs-latest distinction.


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

`NativeSourceElementFreePointer` proves the pinned 817 PUSH64 / 819 MLOAD execution prefix with actual memory-expansion gas and exact memory/world frames. Its six laws retain explicit code, PC, stack-depth and gas hypotheses; this does not establish whole CREATE2 equivalence or enable importer admission. Checked interactively with Lean REPL v4.31.0; production build and global exact-head gates are separately required.
