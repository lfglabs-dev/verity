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
- Imports resolve with the remappings `forge build` (forge 1.5.0) gives solc:
  the written ones (`remappings.txt`, then `[profile.default]` of the
  project's `foundry.toml`) and the ones Foundry infers from `lib/` (or the
  configured `libs`) and from the `remappings.txt` / `foundry.toml` of nested
  libraries (`Compiler/SolidityImport/FoundryRemappings.lean`). Remappings
  apply after relative imports resolve, as in solc. A written remapping wins:
  an inferred one whose name nests with it is dropped. The inferred
  remappings in use go to solc and appear as `inferred remapping` lines in
  `report.toText`.
- Migration from earlier importers: written remappings now follow
  `forge build` (the `remappings` of `forge config`, not the longer list
  `forge remappings` prints). A remapping named after the project's `src`,
  `test` or `script` directory is dropped, and so is a written remapping nested
  under an earlier one (`a/b/=…` after `a/=…`: `a/b/X.sol` is now
  `<a target>/b/X.sol`, the file `forge build` compiles, where earlier importers
  took the `a/b/` target). A written name or target without a trailing `/`
  gains one (`oz=lib/oz` reaches solc as `oz/=lib/oz/`, so `ozx/…` no longer
  matches `oz`). Only `[profile.default]` (or the legacy `[default]`) counts,
  and the first remapping of a name wins. A library's configuration can remap a
  path inside the project, such as `src/sub/`, as `forge build` does.
- Libraries are read only as far as an import needs, at most once per
  `solidity_import`, shown as `remapping scan` in `report.toText`. With
  `auto_detect_remappings = false`, or no library directory, nothing is read.
  Otherwise the library configurations are read (`configs`), since they can
  remap any path, through context remappings too. Every library directory is
  read (`full`) only for an import no written remapping ending in `/` decides
  and whose first directory is not protected (`src`, `lib`, `contracts`, the
  project's `test` and `script`), or that a configuration's remapping could
  match.
- The importer refuses, saying why:
  - an import a context remapping (`context:name=…`) or a library's file
    remapping (`….sol=…`) can reach (not modeled);
  - every import, when a library's `foundry.toml` has a line or key it cannot
    check, uses `extends` or sets the default profile as an inline table, a
    library directory or configuration file is a symlink (Foundry reads through
    it, the importer never follows one) or unreadable, or, with auto-detection
    on, a `libs` entry lies outside the project or has several components (a
    hoisted `../../node_modules`). Remove the cause, or set
    `auto_detect_remappings = false` if the written remappings suffice;
  - an import that needs an inferred remapping whose value depends on
    directory listing order in Foundry, or that needs the full scan while a
    scanned library holds a symlink where Foundry looks (it follows the link,
    the importer does not; symlinks inside `test`, `tests` or `demo` below a
    library's first level do not count) or Foundry's scan depends on listing order or on directories above
    the project root. A protected path or a written match ending in `/` still
    resolves; a remapping written in `remappings.txt` resolves the others.
- Not modeled: a nested `foundry.toml` that is well-formed TOML but which
  Foundry rejects for a value's type (Foundry then ignores that library's
  remappings, the importer does not); environment variables
  (`FOUNDRY_PROFILE`, `FOUNDRY_CONFIG`, `FOUNDRY_REMAPPINGS`, `FOUNDRY_LIBS`,
  `FOUNDRY_SRC`, `FOUNDRY_AUTO_DETECT_REMAPPINGS` and their `DAPP_` forms); the
  global `~/.foundry/foundry.toml`. A project `foundry.toml` using `extends`
  or an inline default profile makes every import refused.
- `solidity_profile` defines an ordinary `Profile` value (reusable,
  `#print`able). `using` takes any `Profile`, named or inline
  (`using { evmVersion := "osaka", ... }`). The settings go to solc and into the
  digest; they should match how the audited bytecode is built. `solc` defaults
  to `0.8.34+commit.80d5c536`, and also accepts pinned 0.8.26, 0.8.10 and
  0.7.6 releases. 0.8.10 requires `viaIR := false` and `evmVersion` up to
  `"london"`; the experimental 0.7.6 boundary is described below.
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

## Experimental Solidity 0.7.6 scalar subset

Select `solc := "0.7.6+commit.7338295f"` explicitly, with `viaIR := false`
and `evmVersion := "istanbul"`. Other legacy EVM targets require separate
admission and execution evidence. The official Linux and
macOS binaries are SHA-256 pinned in the importer and setup script. No pragma
is rewritten and no compiler fallback occurs. The reference fixtures use
Istanbul, optimizer disabled (`runs: 200` retained in standard JSON), and
`metadata.bytecodeHash: "ipfs"`. Other application profiles must retain their
own exact settings; this profile does not assert deployed-bytecode identity.

The initial slice admits unsigned scalar arithmetic (including narrow-width
wrapping), boolean/address/bytes32 values, unsigned/address conversions, scalar
state and mapping reads, conditionals, local assignments, and the admitted internal helper
forms. Function boundaries restore wrapping for 0.7.6 and checked arithmetic
for 0.8; an explicit 0.8 `unchecked` block does not leak into a helper. In
particular a wrap-then-`require` idiom must evaluate the wrapped result before
its explicit guard. Explicit integer-literal casts to unsigned types use the
destination width, so widening `uint8(-1)` to `uint256` yields 255. The declaration
gate checks roots, reached helpers, and the initializers of referenced constants,
including references through other constants. A rejected initializer is reported
at its source location. Functions must be declared `pure` or `view`. State-changing
calls need separate evidence.

ABI coder v1 is the 0.7.6 default. Scalar calldata words are cleaned to their
type rather than rejected for noncanonical upper bits; boolean words normalize
to zero or one. `pragma experimental ABIEncoderV2` and `pragma abicoder v2`
select validation in the target contract's source unit. Inherited functions
use the target contract's decoder, even when their defining file selects the
other coder. Dynamic and aggregate ABI, signed arithmetic, enum conversions,
fixed bytes narrower than bytes32, loops, modifiers, assembly, external calls,
and builtins other than `require`/`revert` are outside this first slice.
Division and modulo are rejected even with a nonzero-looking denominator:
0.7.6 can execute `INVALID`, whereas 0.8 emits a panic payload. Legacy assertions
are likewise rejected. Neither empty `REVERT` nor a 0.8 panic is substituted
for an exceptional halt. These are support boundaries, not claims that the
rejected source is incorrect.

Run the reusable execution campaign and semantic mutations:

```sh
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy --output .lake/legacy-run
python3 scripts/solidity_import_differential.py --mutations \
  --mutant import-legacy-root-checked --mutant import-legacy-helper-checked \
  --output .lake/legacy-mutants
```

The campaign compares original 0.7.6 bytecode, the imported Denote model, and
Verity-generated bytecode. Source compilation targets Istanbul; model Yul uses
0.8.34/Osaka and all bytecode executes on Foundry's Osaka EVM. The retained
manifest identifies both compilers. Gas, historical-fork equivalence, and
source/deployed-bytecode equivalence are not established. Dirty scalar calldata
is exercised for both ABI coders. Each mutation requires an agreeing positive
control and a concrete semantic divergence; build failures/timeouts are errors.

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
| Named call and event arguments | Bind by the statically referenced declaration's names, omitting the receiver parameter for attached library calls. Declaration-order calls, errors and struct constructors keep positional lowering. Reordered scalar internal, library and supported interface calls and events bind parameters, topics and ABI data in declaration order. Legacy solc 0.8.34 and via-IR can disagree on which write or panic occurs first: admit scalar reads with at most one potentially panicking arithmetic operand, or one operand with only literal siblings; otherwise reject at the call. Existing positional type and placement checks still apply. `NamedArgumentsSequence` covers same-typed operands and exact logs. |
| Signed event parameters (development; full release gates pending) | `int256` and `intN` event parameters keep their declared type, so the event signature (topic 0) names them as solc does; the compiled log and the Denote observation both write the sign-extended word. Before, a contract with more than one state variable recorded them as `uint256`, which gave every such event the wrong topic 0. `SignedEventSequence` runs A/B/C with negative and positive, wide and narrow, indexed and unindexed values. |
| Storage array `push` at 2^64 elements (development; full release gates pending) | `push(v)` and `push()` on a storage array of values or structs first check the old length against 2^64 and raise `Panic(0x41)` otherwise, before the new length is written, as solc's `array_push_*` helpers do. Before, the length grew without bound, so element indices past 2^64 aliased other storage. `PushLengthBoundSequence` raises three arrays' lengths to 2^64 − 2 and pushes past the bound (A/B/C, `check_storage_mutations` `import-push-length-*`). |
| Empty storage array `push()` over non-zero storage (development; full release gates pending) | As solc's `array_push_zero_*` helpers, `push()` on a storage array of values or structs grows the length and writes nothing: the new element is whatever its slot held, and `x = a.push()` reads that value. `push(v)` writes `v` into its lane (a struct member by member) and keeps the bits around it. Storage past a length is non-zero once inline assembly lowers the length over written elements; before, `push()` zero-filled the element and `push(v)` zeroed the whole struct first, so the model wrote storage solc leaves alone. `EmptyPushSequence` lowers three arrays' lengths (values, packed `uint64`, struct pairs) through a storage pointer, then pushes and reads the stale elements (A/B/C, `check_storage_mutations` `import-empty-push-*`). |
| Root parameter names that are Yul keywords or builtins (development; full release gates pending) | A root parameter named `caller`, `origin`, `gas`, `let`, … takes `freshFor`'s first free suffixed name (`caller_1`), as locals already did, so the compiled model is valid Yul. |
| `msg.sender`, `address(this)` | Dedicated caller and current-contract expressions, resolved by solc builtin declaration ids |
| `msg.sig` | The left-aligned `bytes4` of the first calldata word, `and(calldataload(0), 0xffffffff << 224)`, resolved through the `msg` builtin declaration id. The same expression in a root, an inlined helper or a modifier (`MsgSigSequence`, fixture `msg-sig`: single and nested mapping keys, storage, internal-call, `abi.encodeCall` and event arguments, custom-error arguments and comparisons, a `bytes4` local read raw by inline assembly, A/B/C against the selectors it equals; control `msg-sig-call-arguments-positive` adds an external interface call argument). |
| Implicit `bytesN` conversions: widening and string literals | `bytesN` values are left-aligned words, so the implicit widening `bytesN` to `bytesM` (`N <= M`) in arguments, locals, assignments, returns and mixed-width comparisons keeps the word (`convert`); implicit narrowing is rejected. A string, `unicode` or `hex` literal where solc expects `bytesN` (helper argument, local initializer, assignment, helper or root return, comparison operand, explicit `bytesN("..")` cast including `bytes32`) is its bytes left-aligned in one word (`fixedBytesStringLiteral?`, `lowerExprAs`); a literal longer than `N` bytes is rejected. Modifier arguments and tuple-return components keep the string-literal rejection. `FixedBytesConversionSequence` (fixture `fixed-bytes-conversions`) runs A/B/C against hex literals and explicit casts. |
| `bytes1`..`bytes31` root parameters, unnamed root returns and explicit casts (all widths) | Root parameters and unnamed root returns resolve through `localParamType` to `ParamType.bytesN n`, and the typed accessor uses `Word (BytesN n)`: the high `n` bytes of the ABI word, low bytes zero. A root parameter word with a nonzero low `32 - n` bytes reverts with empty data, as solc's ABI decoder does. For widths without a dedicated case, and for pairs of dedicated widths that no dedicated case converts (`bytes20(bytes4)`), `bytesN(bytesM)` keeps the word when `N >= M`; narrowing clears the low `32 - N` bytes under via-IR and keeps the stack word under legacy codegen, as solc does (`NarrowStackWordsChecks.bytesWidthCasts`); `bytesN(uint{8N})` shifts the value left by `8 * (32 - N)` bits and `uint{8N}(bytesN)` shifts it back. Integer-literal casts to these widths (`bytes19(0)`), named root returns, and `bytesN` mapping keys, storage variables, event parameters and struct members stay rejected with a located diagnostic. `FixedBytesWidthSequence` (fixture `fixed-bytes-widths`) runs A/B/C with `bytes1`, `bytes19` and `bytes31` parameters and casts, including dirty-padding calldata, against the same values computed on whole words. |
| Narrow `uintN` `for` loop counters (`uint8`..`uint248`) | `lowerFor` accepts any unsigned counter width `N`. When the bound is a literal below `2^N` or of an unsigned type of at most `N` bits the counter cannot wrap and the loop is the same `forEach`. A wider bound runs the body `min(bound, 2^N)` times and then panics with `Panic(0x11)` if `bound >= 2^N`, which is solc's checked `i++` failing after the iteration with `i = 2^N - 1`; inside `unchecked` (the counter would wrap forever) or with `return` / `break` / `continue` in the body that case is rejected with a located diagnostic. Decrementing narrow counters cannot underflow (`i > lower`). `NarrowForCounterSequence` (fixture `narrow-for-counters`) runs A/B/C against a `uint256` counter that performs the checked `uint8` increment itself. |
| `for` loops over a pre-declared counter | `uint256 i; ... for (i = 0; i < n; i++)` (any unsigned width, root or helper): the loop lowers exactly as `for (uintN i = 0; ...)` with the counter scoped to the loop, then the local receives the counter's exit value `n` (the bound is invariant; a narrow counter whose bound reaches `2^N` panics before the store). A non-zero start, a `>` (decrementing) condition, a counter that is not a writable local and a body that `break`s (the exit value would differ) reject with `file:line:column`. `PredeclaredForCounterSequence` (fixture `predeclared-for-counters`) runs A/B/C against loop-scoped counters followed by an explicit store. |
| `for` loop bound `<storage array>.length` | `i < arr.length` where `arr` is a dynamic storage array named by identifiers and member accesses only (a state variable or its struct member, not a storage pointer of unknown provenance; an indexed base such as `m[k].length` keeps the generic bound diagnostic). solc re-reads the length before every test; the importer reads it once before the loop, which is exact when the body cannot change any storage array length: it has no inline assembly or user-defined operator, calls only built-in `pure`/`view` functions and non-virtual modifier-free internal `pure`/`view` helpers whose own bodies preserve lengths (plus events, conversions, struct constructors), and assigns or `delete`s no storage reference (scalar element writes directly into a declared state array or mapping are allowed; writes through member, pointer, or tuple targets are not). Any other body rejects with `a storage array length loop bound requires a body without state-changing calls, inline assembly or storage reference writes`. `StorageArrayLengthBoundSequence` (fixture `storage-array-length-bound`) runs A/B/C against the length cached in a local. |
| `break` / `continue` in inlined helper loops | Inside an inlined helper's `for` / `while` loop (including nested loops and helpers that return early before the loop) a fresh exit flag models the jump: each iteration runs only while the flag is below `2` and first resets it to `0`, `continue` sets `1`, `break` sets `2`, and the statements after one that may jump run only while it is `0`. A `for` loop's counter still advances after `continue`. `Stmt.forEach` cannot terminate early, so a helper `for` with `break` requires an increasing loop with a `uint8` bound or a literal bound ≤256: larger bounds reject rather than running arbitrarily many empty iterations. Helper jumps in `while (!cond)` reject because this condition alone proves no iteration bound. A helper `while` with a conditional break must also use a full-word loop variable: narrow progress operands can retain dirty high bits from assembly. `continue` in a `while` loop (it would skip the loop's final progress step, so solc never terminates) rejects with `file:line:column`; root-level loops still reject `break` / `continue`. `HelperLoopBreakSequence` (fixture `helper-loop-break`) runs A/B/C against structured guards. |
| `bytes` / `string` constants initialized through conversions | A byte constant initializer may wrap its string or hex literal in `bytes(...)` / `string(...)` conversions or name another such constant (`bytes constant B = bytes(NAME)`); the conversions keep the bytes, so the constant lowers as the literal (`constantByteLiteral?`). Any other initializer still fails with `byte constant must have a literal initializer`. `ByteConstantConversionSequence` (fixture `byte-constant-conversions`) runs A/B/C against the literal initializers. |
| Inline-assembly `call` / `staticcall` over memory (development; full release gates pending) | `call(gas(), t, 0, in, inSize, out, outSize)` and `staticcall(gas(), t, in, inSize, out, outSize)` with effect-free operands lower to the closed `YulMemoryCall.module` transport over physical memory: the calldata is `[in, in + inSize)`, the first `min(outSize, returndatasize)` returned or revert bytes are copied to `out`, the result is `0`/`1`. `returndatasize()`, `extcodesize`, fixed-address `mload`/`mstore` below `0x80` and the bubbling `returndatacopy(p, 0, returndatasize())` + `revert(p, returndatasize())` (`Stmt.revertReturndata`) complete the OpenZeppelin 5 `SafeERC20` and `AuthorityUtils` shapes. Values, missing `gas()`, effectful operands, other `returndatacopy` uses and a dirty zero slot reject. A nonempty input range must be a `bytes memory` payload (`add(buf, 0x20)`, `mload(buf)`) or literal bytes below `0x80` that the block's fixed-address `mstore`s wrote unconditionally, and a nonempty output range a payload or written scratch bytes below `0x40`; writes inside an `if` body do not count after it, and `add(buf, 0x20)` is admitted only as a call operand. A fixed-address `mload` below `0x80` must read a scratch word (`0x00`, `0x20`) that an `mstore` at exactly that address in the same block wrote, or the zero slot: anything else there holds what solc's code generator left (mapping-slot hashes, the free-memory pointer), which the model does not reproduce. `let p := mload(0x40)` is admitted only when every use of `p` restores the free-memory pointer (`mstore(0x40, p)`) or places a bubbled revert (the `returndatacopy` + `revert` pair), and a block that overwrites any byte of `0x40`–`0x5f` must restore it with such a `p` before it ends. The call is hoisted ahead of its enclosing expression, while Yul evaluates builtin operands right to left, so an expression is accepted only if everything Yul evaluates before the call (every operand to its right, at every nesting level, including `mload`, `sload`, `returndatasize()`, `selfbalance()` and other calls) is a literal, a plain local or a transaction constant (compound expressions are rejected), and no operand to its left needs hoisting of its own: `and(eq(mload(0x00), 1), call(...))` imports, while `and(call(...), eq(mload(0x00), 1))` and `and(call(...), iszero(returndatasize()))` reject with `Yul external call is evaluated after an operand that could observe it`, and two calls in one expression with `Yul operands left of an external call must not need hoisting` (assign the call to a variable first); `check_yul_memory_call_rejections.py` pins the located rejections and their positive controls. `YulMemoryCallSequence` runs A/B/C against recording call responders. |
| `ecrecover(hash, v, r, s)` (development; full release gates pending) | The global builtin lowers to solc's via-IR sequence over the closed `YulMemoryCall.module` staticcall transport (no new trust assumption: the precompile is the transport's byte-call adversary, as any `staticcall` callee): the four arguments are converted to `bytes32`, `uint8`, `bytes32`, `bytes32` and bound left to right (each copied into a fresh local, so a later argument that reassigns an earlier local does not change its word; `v` is cleaned to 8 bits as solc's ABI encoder does, since an assembly-assigned `uint8` may hold a dirty word), ABI-encoded at the free-memory pointer (not advanced), the output word at `0x00` is cleared, `staticcall(gas(), 1, ptr, 128, 0, 32)` runs, a failed call forwards its return data (`Stmt.revertReturndata`), and the result is `mload(0)` masked to 160 bits, so an invalid signature (the precompile returns no data) is `address(0)`. The legacy pipeline receives the word in a 32-byte allocation at the free pointer instead of at `0x00`; only memory layout differs, which the imported fragment does not observe. A call inside the right operand of `&&` / `||` or a conditional imports (positive controls only: with ample gas the precompile cannot fail, so whether it ran is not observed). `EcrecoverSequence` runs A/B/C (`check_ecrecover.py`) against the real precompile on the EVM and `ecrecover-precompile-v1` (`PrecompileResponderMocks`, a harness-only secp256k1 recovery) in Denote: valid signatures, their high-`s` twins, `v` outside {27, 28} and `uint8(v)` truncation, a dirty assembly-assigned `uint8` `v`, zero and out-of-range `r` / `s`, an `r` that is no curve x-coordinate, random words, a later argument that overwrites the storage or reassigns the local an earlier one reads, and EIP-2612-style permits (valid, replayed, forged, expired) whose digest hashes the nonce consumed by `nonces[owner]++`. `check_ecrecover_rejections.py` pins the positive controls and located rejections; mutants `import-ecrecover-word-order`, `import-ecrecover-argument-copy`, `import-ecrecover-address-mask`, `import-ecrecover-v-cleanup`, `mock-ecrecover-high-s`, `mock-ecrecover-parity` (`check_memory_call_mutations.py`). |
| Typed external calls without return values (development; full release gates pending) | `I(a).f(args...)` as a whole expression statement, where `f` is `nonpayable` or `payable` (called without value) and returns nothing, lowers to solc 0.8.34's sequence: the receiver, then the arguments in source order (scalars, structs, `bytes`/`string` including calldata and `msg.data`, scalar arrays); an empty revert when `extcodesize(a)` is zero; the selector and ABI-encoded arguments in a fresh allocation; `call(gas(), a, 0, p, len, p, 0)` through the closed `YulMemoryCall.module` transport; a failed call's return data forwarded (`Stmt.revertReturndata`); a successful call's return data ignored. Such a call in any other position, and effectful operands, reject. This replaces an earlier lowering through the optional-bool low-level call, which accepted accounts without code and reverted on return data that is not a `bool`. `InterfaceVoidCallSequence` runs A/B/C against recording call responders, an account without code and an EOA, including `enum` arguments (`signal`) and a `nonpayable` call with a `bytes32` result and an `enum` argument (`signalWord`: return data expected, so no code check and a no-data revert on fewer than 32 return bytes). `try I(a).f(args...) { A } catch { B }` on the same calls (a success clause without return variables, one catch-all `catch { }` clause, root or inlined `void` helper) issues the same sequence up to the call and branches on its success bit: a successful call runs `A` whatever its return data (nothing is decoded), a failed call runs `B` (the EVM has rolled back the call's own effects), and an account without code reverts uncaught with no data, as solc does (`tryPing`, `tryRelay`, `tryPoke`). The callee may re-enter. A call after which the clauses and the continuation only compute locals, write memory, return and revert carries `solidity_trailing_low_level_call_reentrancy`; storage reads, storage writes and logs after it, in either form, are admitted when every interaction of the function is a closed transport and carry `solidity_post_call_state_access` (see *Post-CALL storage access and logs*), so sources that update state after the `try` are supported. An interaction that is not a closed transport after the call rejects at the function definition. `try` of `view`, `pure` or value-returning functions, `catch Error(...)`, `catch Panic(...)`, `catch (bytes memory ...)`, call options and named arguments reject with `file:line:column`; `try this.f()` keeps its existing lowering. |
| Namespaced storage struct members (development; full release gates pending) | In a raw-slot (ERC-7201) storage struct, `string`/`bytes` members and mappings with an unsupported key or value keep the slot solc assigns them and reject only when accessed. `mapping(K1 => mapping(K2 => V))` members with a scalar `V` are read and written through both keys: the outer key selects the inner mapping's slot, `keccak256(k1 . (base + offset))`. `NamespacedStructMembersSequence` runs A/B/C. |
| Immutables of value types (development; full release gates pending) | Every immutable of the target chain whose type is a value type other than an enum or a function type (`uint*`, `int*`, `bool`, `address`, `address payable`, `bytesN`, contract and interface types) gets one binding (`bindChainImmutables`). **Argument**: any write in the deployment code, whatever its shape (conditional, repeated, tuple, `delete`, `++`, `--`, over an inline initializer) and wherever solc accepts it (constructor bodies and their base-constructor and modifier arguments, any state variable's initializer, inheritance-specifier arguments; `chainDeploymentCode`), makes the value one the source does not determine; it reads as `Expr.immutable NAME`, and the synthesized constructor installs it from an argument of the immutable's own type (`Expr.constructorArg i`, validated like an ABI parameter: a dirty word reverts, as in solc), so deployments and proofs supply it. The one exception is an `address` immutable whose only write in the deployment code is a top-level `NAME = address(this)` in a constructor body with no `return` and no modifier (base constructor specifiers aside): it reads as `Expr.contractAddress`. **Installed**: never written, with an inline initializer that lowers, without statements, to literals, the deployment environment (`msg.sender`, `tx.origin`, `address(this)`, `block.chainid`, `block.number`, `block.timestamp`) and pure word operations (`deploymentInitializerEnv?`): it reads as `Expr.immutable NAME`, and the synthesized constructor evaluates the initializer at deployment, as solc does. **Read**: never written and without an initializer reads as `0`; never written with a literal-only initializer reads as that value. Initializers that read storage, memory or any immutable (directly or through a helper: initializers run before the constructors, so another immutable may not hold its final value yet, and every immutable of the chain is unbound while one is lowered) or call anything, and enum or function-typed immutables, stay unbound: their reads and getters keep the located `immutable state variable NAME is outside this slice` rejection. Public getters of bound immutables return the binding. `model.immutables` declares installed and argument immutables in declaration order. Denote reads them from `DenoteState.immutable`; `executeBody`, `AllEntryPointsPreserve` and `AdversarialEntryPointSequence` take the deployment's `immutables`, fixed for a whole sequence, and `SequenceRunner` rejects a value outside the immutable's type. `ImmutableAddressSequence` runs A/B/C with constructor arguments taken from distinct funded senders; `ImmutableScalarSequence` runs it over `uint256`, `uint64`, `uint8` (conditionally written), `bool`, `bytes32`, `bytes4`, interface-typed, `address payable` and `int16` arguments (every route deploys clean words; each dirty narrow word alone must make both the source and the compiled deployment revert with the same data, as solc validates constructor arguments), `msg.sender` and `block.chainid` initializers, `uint256`, `bool`, `int16` and `bytes4` literal initializers, an unwritten immutable, and immutables written by `++`, an unchecked `--` and another immutable's initializer. `Expr.immutable` is an atom (`isAtom`, `isOrderIndependentSibling`), like `Expr.param`: it is total, effect-free and fixed for the deployment, so it can be a custom-error argument or a call operand without a binding. |
| `block.timestamp`, `block.number`, `block.chainid`, `block.basefee`, `tx.origin`, `tx.gasprice`, `address(this).balance` | Dedicated transaction- and account-context expressions (`Expr.blockTimestamp`, `Expr.blockNumber`, `Expr.chainid`, `Expr.baseFee`, `Expr.txOrigin`, `Expr.gasPrice`, `Expr.selfBalance`), including `payable(address(this)).balance` and Yul `selfbalance()` / `origin()` (Yul `basefee()` / `gasprice()` are rejected: they never reached the Yul arity table; no differential route pins a base fee or gas price, so `block.basefee` / `tx.gasprice` import without an A/B/C value check) |
| Ordinary nested root blocks | Ordered recursive lowering with unique local bindings, lexical lookup restoration, and propagated unconditional returns; unsupported nested control flow and statements after return reject with source locations |
| Calldata bytes helpers and modifier arguments | A parameterized internal helper can directly return a `bytes calldata` parameter, slice, or nested calldata helper result. The offset and length remain in calldata through indexing, slicing, `.length`, fixed-bytes casts, `abi.decode`, and calls to another calldata helper; hashing and `bytes memory` copies clear trailing partial-word bytes as `solc` does. Range failures revert with empty data, while indexing past the result panics with `0x32`. A modifier with one top-level placeholder can bind a calldata bytes parameter, slice, or helper result alongside scalar arguments captured at modifier entry. Named or multi-statement calldata helper results, potentially selector-crossing `msg.data` slices passed as ordinary descriptors, and reassignment of calldata modifier parameters are unsupported. `msg.data[4:]` and other slices with a literal start at least 4 can be bound or decoded as ordinary calldata. Eager binary expressions follow the selected solc pipeline's operand order recursively (right-to-left under legacy, left-to-right under via-IR); `&&` and `||` remain short-circuiting. In legacy mode, an attached library call with a computed calldata bytes receiver and nonliteral arguments rejects: legacy evaluates the receiver last. `CalldataBytesHelperModifierChecks` compares return words, memory-word padding, post-placeholder scalar captures, revert bytes, and nested modifier writes with solc. |
| Explicit scalar/tuple return | `returnValues`, preserving order |
| Flat nested storage structs | `records[k].part = p` copies a memory or calldata struct into the selected packed storage members. `return records[k].part` returns those members in declaration order. Array, mapping and further struct members inside the copied value are unsupported; unrelated siblings are not copied. |
| Default scalar locals (development; validation pending) | Uninitialized unsigned integers, address, bool and bytes32 bind a fresh local to zero; reference and unsupported scalar defaults reject at the declaration |
| Scalar local writes (development; validation pending) | `=` and `delete` on materialized scalar locals; converted RHS evaluated before assignment; lexical shadowing retains declaration identity; compound writes and parameter writes reject |
| Invariant scalar `for` (development; validation pending) | uint256 counter from zero, strict `<`, increment by one; literal/parameter/unwritten-local bounds; body return/revert preserved; body counter writes, mutable bounds, break/continue reject |
| Empty `revert()` and ABI rejection payloads (development; full release gates pending) | Explicit `Stmt.revertEmpty` compiles to `revert(0,0)` and Denote observes exactly zero bytes, independent of memory and the current return-data buffer. Source scalar/struct guards, getter bounds and bare builtin revert keep their existing conditions and source-position rejections. Other external calls remain outside admitted source support. |
| Typed-interface word staticcall (development; full release gates pending) | `I(addr).f(args)` where `f` is a `view` function of an interface whose parameters are scalar ABI words (`paramType`: `address`, `address payable`, contract types encoded as `address`, `uint256`, narrow and signed integers, `bytes32`, `bytes4`, `bool`, `enum`) and which returns one `uint256`, `int256`, `bytes32`, `bytes4`, `bool`, `address` or `uint8`, and `addr` is an `address` converted to the interface or an identifier of interface type, in any expression position. The lowering does not depend on whether the contract has one or more state variables (#2830, `InterfaceStaticCallStateCountChecks`): binary operands follow each pipeline's order (legacy right-to-left, via-IR left-to-right), conditional arms and short-circuit operands run only on their branch, and internal-call arguments run left to right. Arguments of exactly the parameter type that lower without prelude statements take the word path below; converted, computed or call arguments are converted and cleaned after `checkEncodingScalar`. Lowers to the closed `SolidityStaticCall.uint256Module` ECM: selector and cleaned argument words (`address` masked to 160 bits, `bool` normalised to `0`/`1`) stored at the free pointer, `staticcall(gas(), addr, p, 4 + 32n, p, 32)`, a failed call's complete return data forwarded as the revert payload, fewer than 32 success bytes revert with no data (including accounts without code), the first word decoded and extra bytes ignored; a `bool` other than `0`/`1`, an `address` at or above `2^160`, a `uint8` at or above 256 or a left-aligned `bytes4` with nonzero low 28 bytes reverts with no data, as solc's decoder does. Every complete word is a valid two's-complement `int256`. Short-circuit operands keep the call inside the branch Solidity evaluates; a `require` condition, call included, is evaluated before the error arguments, matching via-IR. Denote executes the same request against an explicit byte adversary. A whole scalar root return may also compare a `bytes4` call with a type-qualified function selector using `==` or `!=`; that operand is a constant. Otherwise, non-view/pure callees, other parameter types (dynamic and struct parameters in a contract without state variables), other return shapes, arguments `checkEncodingScalar` rejects (including a nested call argument), side-effecting word-path arguments, noncommuting reordered arguments, call options, non-interface receivers, `address payable` receivers, error-argument placement, an assignment statement whose target is an array element (memory arrays included, conservatively) or a computed mapping key and that makes or may make a typed interface call, directly or through internal callees, function values passed to them, `super` and modifiers (solc evaluates the right-hand side before the target's keys and bounds checks; `checkInterfaceCallAssignmentOrder`) and `try` reject with `file:line:column`. `enum` parameters (#2719), admitted on the same route as narrow scalar parameters, are encoded as their ordinal word: solc's encoder asserts the ordinal is below the member count, and every enum value the importer admits already is (entry guards, `Panic(0x21)` casts, fallible casts in arguments and enum storage rejected). `InterfaceStaticCallSequence` (parameterless `uint256`) and `InterfaceWordStaticCallSequence` (word and `enum` arguments, `bool`/`bytes32`/`bytes4`/`int256` returns, short-circuit and `require` placement) each run three equivalent variants A/B/C, against selector-checked and calldata-folding oracle mocks respectively, plus an account without code. |
| SSTORE2-style `create2` code storage (development; full release gates pending) | Yul `create2(0, add(buf, 0x20), mload(buf), salt)` (offset operands in either order) as the whole value of a Yul assignment or `let`, in roots or inlined helpers, where `buf` is an unshadowed, never-reassigned `bytes memory` local initialised by `abi.encodePacked(p, ...)` or `bytes.concat(p, ...)` and `p` is a hex literal (or constant) whose bytes start a checked `DenoteCreate2.templateCost` initcode template. Lowers to the closed `SolidityCreate2.module` ECM: the compiled model emits `create2` over its own memory, and Denote runs `Create2Opcode.execute` on the frame's physical byte memory with the instrument-supplied parent gas, binding the created address or zero and committing code, nonces and balances to `ContractState.accountWorld`. Nonzero/computed values, other offsets, sizes or buffers, unchecked prefixes (including other SSTORE2 prefixes), nested `create2` and `create` reject with `file:line:column`. |
| Struct event parameters (development; full release gates pending) | `emit E(...)` whose non-indexed parameters include a struct passed as a memory struct variable, alongside indexed value-type parameters (`uint*`, `address`, `bool`, `bytes32`). The non-indexed arguments are encoded exactly as `abi.encode(...)` (dynamic struct members included) and logged by the closed `SolidityLog.module` ECM with solc's `eventSelector` as topic 0 and cleaned indexed topics; Denote reads the payload from physical memory. Indexed structs, narrow fixed-bytes/enum/dynamic indexed parameters, struct constructors and storage structs as arguments, and anonymous events reject with `file:line:column`. `Create2BytecodeAndStructEmitSequence` runs three equivalent variants A/B/C with trace-discovered deployment accounts. |
| Non-indexed `string` event parameters (development; full release gates pending) | `emit E(...)` whose non-indexed parameters include `string` (a `string memory` / `string calldata` variable, a string literal, `string.concat(...)` or `string(abi.encodePacked(...))`), beside indexed value-type parameters and other data. They take the struct-event path: the non-indexed arguments are encoded exactly as `abi.encode(...)` (offset, length, right-padded bytes) and logged by the closed `SolidityLog.module` ECM with solc's `eventSelector` as topic 0. Because topics are lowered before the data while solc evaluates event arguments left to right, every non-indexed argument (string or value type) that precedes an indexed argument must be a variable or literal; a computed one rejects with `file:line:column`. Indexed `string` parameters (a keccak topic) still reject. `StringEventParamSequence` runs three equivalent variants A/B/C. |
| `<address>.code.length` and optional-bool low-level `.call` (development; full release gates pending) | `<addr>.code.length` on an `address`-typed account other than `address(this)` lowers to the closed `SolidityExtCodeSize.module` ECM (`extcodesize`); Denote reads `DenoteExternalCode.extCodeSize` over `ContractState.accountWorld`. The Solady/OpenZeppelin `SafeTransferLib` sequence `(bool success, bytes memory returndata) = target.call(abi.encodeCall(f, (args...)));` `if (!success) { assembly { revert(add(returndata, 0x20), mload(returndata)) } }` `require(returndata.length == 0 \|\| abi.decode(returndata, (bool)), reason);` in roots and inlined void helpers, where `f` is an external function whose parameters are `address`, `bool`, `bytes32` or `uint256`, lowers to the closed `SolidityLowLevelCall.optionalBoolModule` ECM followed by the same `reason` check of its result: the value-free `CALL` of `selector ++ words` written at the free pointer (advanced after the call), a failed call's complete returndata forwarded, empty returndata accepted, non-empty returndata shorter than a word or whose first word is not `0`/`1` reverting with no data, and a decoded `false` failing `reason`. Denote issues `DenoteByteExternalCalls.callBytesRequest` to the explicit byte adversary and keeps its committed world; `DenoteLowLevelCall` relates the result to `decodeOptionalBoolCall`. Call options (`{value: ...}`, `{gas: ...}`), unbound or unvalidated returndata, missing forwarding, strict or other validations, other reads of `success`/`returndata`, non-`abi.encodeCall` or dynamic-parameter calldata, stateful operands, other placements (expression statements, helpers with returns), `staticcall`/`delegatecall`, `address(this).code.length` and other `.code` reads reject with `file:line:column`. `ExternalCodeAndLowLevelCallSequence` runs three equivalent variants A/B/C against recording call responders, an account without code and an EOA. |
| `<address>.codehash` (development; full release gates pending) | `<addr>.codehash` on an `address`-typed account other than `address(this)` is a `bytes32` value lowered to the closed `SolidityExtCodeHash.module` ECM (`extcodehash`); Denote reads `DenoteExternalCode.extCodeHash` over `ContractState.accountWorld` with EIP-1052 semantics: `0` for an empty account (nonce `0`, balance `0`, no code), `keccak256("")` for an existing account without code, otherwise the Keccak-256 of its runtime code. Comparisons with `bytes32` constants, custom-error reverts, `require`, locals, storage and mapping writes and internal helpers compose with it. `address(this).codehash`, a read whose lowered operand may be the executing contract (a local or parameter bound to `address(this)`) and `codehash` as a custom-error argument reject with `file:line:column`; a codehash read that runs after a low-level call or `create2` in program order rejects, because the call can create or fund the account it reads. Constructors are not imported, so the constructor-time binding check of the motivating pattern is outside this slice. `ExtCodeHashSequence` runs three equivalent variants A/B/C over three coded accounts, an account created with empty runtime code (nonce 1, no balance), two funded EOAs (nonce > 0 and nonce 0), a never-touched address and a precompile address. |
| `<address>.code` and dynamic-struct `abi.decode` returns (development; full release gates pending) | `<addr>.code` on an `address`-typed account other than `address(this)`, as the `bytes` operand of `abi.decode` or the initializer of a `bytes memory` local, lowers to the closed `SolidityExtCodeCopy.module` ECM: solc's `external_code_at` (`extcodesize`, a fresh `bytes memory` allocation at the free pointer with `Panic(0x41)` on 64-bit overflow, the length word, then `extcodecopy`); Denote copies `DenoteExternalCode.accountCode` from `ContractState.accountWorld` into physical memory. `abi.decode(data, (S))` from a `bytes memory` buffer, where `S` is not flat and its complete `AbiSchema` holds only unsigned scalars and dynamic arrays of unsigned scalars or of flat scalar structs, materializes `S` in solc's memory layout (`AbiMemoryDecode`: solc's `abi_decode_*_fromMemory` checks, eager `Panic(0x41)` allocation, zero-byte revert for every other malformation) as a single `S memory` local or a root return value. Roots with an unnamed `returns (S memory)` for such an `S` return `abi.decode(...)` or a memory struct variable with a complete schema (including `S memory` parameters): the struct is re-encoded by the shared `abi.encode` lowering and returned by the closed `SolidityReturnMemory.module` ECM (`return(ptr, size)`); Denote stops with the buffer's words in `observedReturnWords`. `address(this).code`, other `.code` uses (`keccak256(a.code)`, `a.code[i]`), calldata sources, extra decode targets, `bytes`/nested-struct/fixed-array members, named returns, calldata-struct and helper-call returns, reassigned decoded locals, member access on a decoded value and tuple returns reject with `file:line:column`. `ExtCodeCopyStructDecodeSequence` runs three equivalent variants A/B/C over code stored by the checked CREATE2 transport, including malformed payloads. |
| Schema ABI array-length `for` (development; validation pending) | Memory/calldata array length captured after its exact initial decoder; recursively checked body preserves memory headers; memory writes and external calls reject |
| Local declarations and storage aliases | Bindings named after the Solidity local (suffixed `_1`, `_2`, ... on collision), or resolved read paths |
| Scalar storage reads, `=`, and `delete` | Resolved uint8–uint256, address, bool, and bytes32 fields; exact solc slots and packed offsets; masked writes preserve neighboring bits and bool reads/writes normalize to 0/1 |
| Root fallthrough, bare `return;`, and named root return parameters | Void roots emit `stop` on fallthrough or bare `return;`; roots whose return parameters are all named scalars initialize each to zero, allow body reads/writes, and emit `returnValues` on bare `return;` or fallthrough; empty-body scalar hooks return zero words |
| One/two/three-key mappings to structs | solc slots, word offsets, and packed uint offsets (three-key mappings hash the outer two keys via `keccak256(abi.encode(k2, keccak256(abi.encode(k1, slot))))`) |
| One/two/three-key scalar mappings | address/uint256/bytes32/int256/bool/enum keys; uint8–uint256, int256, address, bytes32 and bool values; root assignment and `delete`, with masked narrow writes |
| Events | Resolved non-anonymous scalar events, including qualified library declarations, up to three indexed arguments and exact source-order data. Arguments must have total scalar preludes; in scalar events (not the struct/array/`bytes`/`string` event path), scratch-space hashing writes (`mstore` at 0x00/0x20, e.g. a member read of a mapping nested in a mapped storage struct) count as total (`EventNestedMappingReadSequence`). An inlined helper's reassignment of its own result, parameter or local (`r = a; r = r ^ 0x55;`, a multi-statement Yul result) counts as total when it writes a binding the same argument's prelude declared earlier, whatever the number of state variables (formerly only with more than one; `EventHelperPreludeStateCountChecks`, #2830). An event with such a nested read is admitted only when at most one of its arguments can revert (e.g. a read keyed by a bounds-checked array element), since via-IR evaluates event arguments left to right while legacy codegen evaluates indexed arguments last to first; competing revert paths and arguments containing assignments (`=`, `++`, `--`, `delete`) reject with `file:line:column`. Narrow unsigned event arguments require either a direct parameter of the declared type or an in-range canonical integer constant literal (`n < 2 ^ bits`); anonymous/dynamic events, noncommuting reordered arguments and conflicting declarations reject with source locations. |
| Short-circuit boolean expressions and `!` | `&&` and `||` evaluate the left operand once; the right operand, including guards and helper preludes, executes only in its selected branch. Prefix `!` on a `bool` operand lowers to `Expr.logicalNot`. Unsupported constructs still reject even in unreachable operands. |
| `if` / `else` statements | Root statements lower to `Stmt.ite` on a boolean condition evaluated once; a branch `return` or `revert` stops execution and the continuation runs only on fallthrough. In inlined single-value helpers, the continuation after a returning branch is lowered once into the other branch and both results assign one fresh local; in inlined void and multi-return helpers, nested early `return` inside `if`/`else` lowers the post-conditional continuation into the fallthrough branch(es) after restoring branch-local lexical scope. Unsupported constructs still reject in unreachable branches. |
| Numeric literals and units (development) | Exact integral decimal/scientific/hex literals, including leading-dot fractions and digit separators, unsigned/bool named constants, and bounded sums of exact natural constant operands; seconds, minutes, hours, days, weeks, wei, gwei, ether. Fractional results, oversized words and general rational constant expressions reject. Focused checks pass 96 A/B/C transactions, 56 acceptance/rejection controls and 16 semantic mutants with minimal witnesses; the numeric parent `b0fa7b0e2` passed all 12 exact-head gates. |
| Exact natural constant products (development) | `int_const` multiplication of two lowered natural literals with empty preludes uses unbounded arithmetic and requires a uint256 result. Includes `100 * 365 days`; fractional operands, oversized intermediates and general rational operations reject. Focused checks at `bbc8fe0ad` pass 96 A/B/C transactions, 60 acceptance/rejection controls and a product mutant with a replayed minimal witness; full exact-head gates pending. |
| Inline constant array reads (development) | A directly indexed unsigned fixed array of exact natural constants lowers to a bounds guard (panic `0x32`) and value selection. Named constants are supported; nonconstant/guarded elements and other element types reject here. Literals used as values (bound to locals, passed, returned) are memory arrays (fixed-size memory array slice). Focused checks at `674cd89cd` pass 96 A/B/C transactions, 67 acceptance/rejection controls and three detected mutants with replayed minimal witnesses; full exact-head gates remain pending. |
| Unsigned modulo (development) | Typed unsigned `%` uses EVM remainder after a zero-divisor guard that panics with code `0x12`; narrow operands retain their declared unsigned width. Signed `%` is the `int256` row of the signed slice below. General constant/rational modulo rejects. Validation pending. |
| ABI array length (development, unvalidated) | Candidate `.length` lowering for schema-checked scalar or flat static-struct arrays inside memory/calldata struct parameters. Memory uses the materialized header; calldata checks the lazy header at source access. A/B/C fixtures, malformed inputs and two mutants are prepared; native validation and release gates remain pending. Storage arrays and other schemas remain unsupported. |
| Scalar ABI canonicality | Raw `uintN`, address and bool words are checked before source execution, including unused parameters. Noncanonical words revert with empty bytes. Complete-word A/B/C checks exercise mixed parameter positions; dynamic struct and partial-byte ABI validation remain outside this instrument. |
| Boolean literals | Resolved `true`/`false`; canonical 1/0 values |
| Flat static memory/calldata struct parameters | Full tuple ABI including unused scalar members; indexed field bindings and complete head sizes. Memory members are validated at entry; calldata members are validated when read, preserving competing reverts. |
| Dynamic memory/calldata structs (experimental) | Complete unsigned-scalar roots with dynamic scalar arrays or arrays of flat scalar structs. Full ABI signature, eager memory materialization and lazy calldata reads; direct element indices only. No legacy member projection. Mixed static/dynamic struct parameters and computed element indices reject precisely. Permanent fixtures cover a multi-file imported nested dynamic struct (`NestedDynamicStructAbi`, 408 A/B/C controls, four variants), scalar arrays (96 controls, three variants), and two dynamic roots (132 controls, four variants). Twenty dynamic ABI mutations are detected and minimized. Generated-name collision is checked against the actual decoder binding. Whole-library proof compatibility passes; exact-head campaign gates remain pending. |
| Unsigned `+`, `-`, `*`, `/` | Word arithmetic with overflow/underflow/zero-divisor panics |
| Unsigned comparisons, equality | Scalar conditions |
| `require(condition, "message")` | Exact `Error(string)` bytes; UTF-8 literal messages, including empty strings, in roots and inlined helpers |
| `require(condition)` | Reverts with empty returndata when the condition is false, in roots and inlined helpers; admission no longer depends on the number of state variables (#2830). `BareRequireStateCountChecks` requires identical models for a one-slot and a two-slot contract on both pipelines. Event arguments whose guards revert with different payloads (an inlined `require` in one argument, an out-of-bounds index in another) reject with `file:line:column`: legacy evaluates indexed arguments last to first, via-IR left to right. In events with a struct, array or `bytes` parameter, a data argument before a guarded indexed argument must also be a variable or literal. |
| `assert(condition)` and discarded expression statements (`x;`, `this;`, `a / b;`, `arr[i];`, `!f();`) (#2843) | `assert(c)` (builtin declaration `-3`; a user function named `assert` stays an ordinary call) evaluates `c` once, effects included, and reverts with `Panic(0x01)` when it is false (`lowerAssert`), in roots, loops and inlined helpers; a condition that panics itself keeps its own panic code. An expression statement whose value is discarded (`lowerDiscardedValue`) is still evaluated on both solc 0.8.34 pipelines, with or without the optimizer (checked on Anvil): an identifier (`this` included) or a literal lowers to nothing; a binary or unary operation (`-`, `!`, `~`), an index or member access, a parenthesized value, a conditional with values and a type conversion lower as a value bound to a fresh local, so their checks keep their panics (`10 / y;` `0x12`, `y - 1;` `0x11` outside `unchecked`, `arr[y];` `0x32`, `Mode(y);` `0x21`) and their calls their effects. Located rejections naming the statement kind (`AssertStatementChecks`): a conditional between calls without return values (`c ? f() : g();`), a struct constructor, a tuple or inline array and any other expression kind (`uint256;`); a value the expression lowering does not support keeps that lowering's rejection. `AssertStatementSequence` (A/B/C check `assert-statement`; mutants `import-assert-panic-code`, `import-discarded-value-evaluate`, `import-discarded-conversion-evaluate`). |
| `revert(message)` and `require(condition, message)` with a computed `string memory` message | `string(abi.encodePacked(...))`, `string.concat(...)`, string helpers (OZ `Strings.toHexString`), `string memory` locals/parameters and `string calldata` parameters. The condition, then the message, are evaluated unconditionally (solc 0.8.34 via-IR order, so a reverting message helper reverts even when the condition holds); only the `Error(string)` encoding (selector, offset word, length word, zero-padded bytes) is on the failing path. The payload is reverted by the closed `SolidityRevertMemory.module` transport (`revert(ptr, size)`); Denote reverts with exactly the buffer's bytes. Storage `string` messages reject with `file:line:column` (`unsupported revert message type string storage ref`). `DynamicRevertStringSequence` runs three equivalent variants A/B/C. |
| `require(condition, CustomError(args))` and `revert CustomError(args)` | Resolved static unsigned/address/bool/bytes32 errors; arguments restricted to decimal numeric literals or scalar bindings; exact selector and ABI words (`revert CustomError(args)` lowers to `.requireError (.literal 0) name values`) |
| Narrowing casts | Bit masks, not overflow checks |
| Ternaries | Lazy `ite` branches |
| Resolved acyclic helper calls | Inlined single-value, void, and multi-return internal/private bodies with separate local scopes, including C3 virtual override resolution across `linearizedBaseContracts`, diamond `super.fn(...)` resolution, explicit base-qualified `Base.fn(...)` calls, and empty-body scalar virtual hooks |
| ABI encoding and Keccak (experimental) | `keccak256` over static scalar `abi.encode`, a single complete supported root struct, literal byte buffers and `abi.encodePacked` of unsigned/address/bool/bytes1/bytes4/bytes32 scalars, narrow signed integers (`int8`..`int248`, packed into their own width as the low bytes of the sign-extended word; `PackedSignedIntSequence`, fixture `packed-signed-int`, mutant `import-packed-signed-width`) and admitted byte buffers. Packed buffers preserve exact byte widths and lengths using aligned word memory; nested buffers receive separate allocations. Hex numeric literals retain their exact value. Dynamic byte parameters, arbitrary byte locals, direct packed structs, fixed-byte widths other than bytes1, bytes4 and bytes32 and effectful scalar arguments remain rejected. The focused 96-case A/B/C campaign includes an imported library key derivation over a complete dynamic root (`RecordHashLib.toKey`, byte-pinned in `imported-types/manifest.json`), storage/events and rollback. All four generated variants agree, 15 semantic mutants are detected with minimized witnesses, and 11 located rejection/acceptance controls pass on captured local snapshots. Copy-loop and packed-allocation helper proofs are in `AbiMemory`; exact-head release gates remain pending. |
| Internal struct reference arguments | Root memory-to-memory and calldata-to-calldata references retain the exact ABI descriptor and nominal struct declaration identity across acyclic single-return helpers, including internal library receivers. External reference helper calls and raw Yul pointer access reject. Static and dynamic roots preserve eager memory/lazy calldata validation. Cross-location copies, storage references and unsupported reference expressions reject with source locations. Twenty A/B/C cases across four equivalent variants and a wrong-root mutation cover this rule; located rejection mutations cover external-call boundaries, location conversions and Yul name shadowing. |
| Single assignment to a named assembly return | `xor`, `mul`, `lt`, as in `UtilsLib.min` |

Non-empty roots with unnamed return parameters must return explicitly on every non-reverting path. Payable roots are rejected until value-transfer
semantics are supported. Other `msg`, `block`, and `tx` context members are
rejected when reached. Loops, mapping-to-struct writes, compound assignments, external calls
(other than the typed-interface staticcall, checked-template `create2`, optional-bool
low-level `.call` and `<address>.code` rows above),
external library calls (a `public` or `external` library function called from
outside its library, directly or through `using for`: solc emits a
`DELEGATECALL` to the library linked at deployment, whose code the source does
not determine; internal library functions, and public ones called by name
inside their own library, are inlined),
modifiers, recursion, named call arguments, signed
operations, and any other construct reached from a root are rejected with
`file:line:column`, the construct, the reason, and the call path from the root
(`closure: C.f -> L.unused`). Functions outside the closure are listed as
excluded and do not block the import. Only reached storage fields are decoded;
array, mapping, `string` and `bytes` struct members are reported as opaque and cannot be read.

## What each check establishes

Four questions are answered separately, per root; none implies the next.

1. **Importable.** The command succeeds, or fails with the diagnostic above.
   A partial model is never produced, so every listed root is importable.
   Under `collectUnsupported` a root can instead be `unsupported`; such a
   root proves nothing and the import defines no model
   ([below](#collecting-every-unsupported-construct)).
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

### Shortcuts used

A few inline-assembly blocks are not translated: when a block's `yulBlockFingerprint`
equals the fingerprint of a trusted shortcut, the importer uses that shortcut's fixed
lowering instead (see "Trusted shortcuts" under [Trust boundary](#trust-boundary)). The
report lists each such replacement under the root whose model uses it
(`FunctionStatus.shortcuts`), in both `toText` and `statusText`. The names it prints come
from the registry entry (`trustedImporterShortcuts`) and the lowering's own declaration:

```text
status loadSlots importable denoteCovered true compilerProof unavailable (...)
  shortcut extsloadBatchYulFingerprint lowering lowerBatchArrayLoadShim fingerprint <sha256> at TailAssemblyArrayRead.sol:12:9
```

A root without such a line uses no shortcut. The differential `describe` output
lists the same fingerprint names under `shortcuts`.

## Collecting every unsupported construct

By default the importer stops at the first construct it cannot lower. For an
inventory of what a contract needs, set `collectUnsupported := true` in the
profile:

```lean
solidity_profile survey where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"
  collectUnsupported := true
```

The flag is not a solc setting and is not part of the digest. With it, a
failure is recorded and lowering continues:

- **Recovery points.** Every variable declaration, expression statement and
  `emit`, wherever it is lowered (roots, inlined helper and modifier bodies,
  loop bodies), and every statement of a root body (`if`, loops, `return`,
  inline assembly, ...). A failure inside a structural statement of a helper
  (its `return`, `if` or loop) is recovered at the enclosing statement. A
  failure outside any statement (parameters, modifiers, return types) is
  recovered for the whole root. There is no expression-level placeholder: the
  failing statement is skipped.
- **State.** A recovered statement leaves no trace: the importer state is
  rolled back to its value before the statement (`StateT` discards the failed
  branch), so a root never continues from a half-lowered statement. A root
  with a recorded construct is rolled back entirely and contributes nothing
  to the closure, fields or projections of the import.
- **Root list errors.** A root that cannot be selected, a root imported
  twice, and two roots with the same name (`root function name collision`,
  e.g. two overloads) are errors in the command, not unsupported constructs.
  They are not recovered: the import fails as without the flag, whatever the
  root order and whether or not the earlier root is unsupported.
- **Follow-on failures.** Skipping can cause later failures, e.g. a read of a
  local whose declaration was skipped. An entry is tagged
  `[possibly consequential: ...]` when it reads a variable declared in a
  skipped statement, or when it is a root-level failure after an earlier
  skip. Untagged entries are not proved independent either: the list is every
  failure at a recovery point, in source order, not a minimal or exact set of
  blockers. Clearing one entry may expose constructs it hid.

Each root with a recorded construct is `unsupported` in the report; `toText`
renders its entries (position, AST node kind, reason, closure path) under its
`status` line. From `CollectUnsupportedSurveyChecks`:

```text
status first unsupported constructs 4 denoteCovered false compilerProof unavailable (...)
  CollectUnsupportedSurvey.sol:12:26 Identifier: builtin call is outside this slice (closure CollectUnsupportedSurvey.first -> CollectUnsupportedSurvey.scaled)
  CollectUnsupportedSurvey.sol:13:20 Identifier: unresolved identifier 17 (closure CollectUnsupportedSurvey.first -> CollectUnsupportedSurvey.scaled) [possibly consequential: reads budget bound by a skipped statement]
  CollectUnsupportedSurvey.sol:17:9 DoWhileStatement: unsupported statement DoWhileStatement (closure CollectUnsupportedSurvey.first)
  CollectUnsupportedSurvey.sol:19:18 MemberAccess: unsupported block context member prevrandao (closure CollectUnsupportedSurvey.first)
```

If any root is `unsupported`, the command succeeds with a warning listing
these lines and defines **only** `x.report`: there is no `x.model`, no
`x.covered`, no `x.sourceDigest` and no accessor, so no proof, differential
run or compilation can use the import. **An `unsupported` root proves
nothing**, and the `importable` roots of such an import have no kernel-checked
`covered` theorem either; import them again without the flag. If nothing is
recorded, the flag changes nothing: model and report equal the flag-off
import (`CollectUnsupportedSurveyChecks`).

## Trust boundary

solc's AST and storage layout, and the lowering in `Import.lean`, are trusted.
Inlined helper bodies are the code solc compiles into the contract. Code that
runs behind a `DELEGATECALL` to a linked library is chosen at deployment and is
never inlined (`check_library_call_rejections`).
The model is built as ordinary values and quoted (`Quote.lean`); after
elaboration the definitions are evaluated back and must equal those values.
The digest (`sourceDigest`) is SHA-256 over framed JSON of the importer
version, the solc release, the contract name, the selected signatures, the
complete solc input (sources and settings), and `importerSources`: the SHA-256
of each importer source file, keyed by its path relative to the importer's
source root. `Compiler/SolidityImport/SourceDigest.lean` computes that file set;
nothing lists it by hand:

- every module in the import closure of `Compiler.SolidityImport.Import` that
  has a source file under the source root. That includes the execution
  semantics the model is interpreted by (`Verity.Core.Model.Denote` and its
  imports) and `Compiler.CompilationModel`. Lean core, Std and other packages'
  modules are not hashed;
- every regular `.lean` file under `Compiler/SolidityImport/`, imported or
  not, except test files (names ending in `Test.lean` or `Tests.lean`), hidden
  entries and symbolic links. The modules such a file imports are hashed only
  when `Import` imports them too (for example `Verity.Core.Model.Denote` is,
  `DenoteByteExternalCalls` is not).

So editing any non-test importer file changes the digest of an unchanged
contract (`SourceDigestTest.lean` checks the closure, the directory and the
wiring into the digest input). Lake re-elaborates an import, and so recomputes
its digest, only when its traced inputs change. Its import graph covers the
closure. The `solidityImporterSources` input in Verity's `lakefile.lean` covers
the other directory files for the smoke imports; a downstream package does the
same with
`input_dir verityImporter where path := ".lake/packages/verity/Compiler/SolidityImport"`
(`filter := .extension "lean"`) in its library's `needs`. The statement
denotation retains exact panic bytes; legacy scalar accessors erase failure
bytes. Gas, public ABI decoding and bytecode equivalence remain outside the
import certificate.

**Trusted shortcuts.** Three inline-assembly blocks are not translated. When a block's
`yulBlockFingerprint` (SHA-256 of its solc Yul AST without source positions) equals the
fingerprint of an entry of `trustedImporterShortcuts`
(`Compiler/SolidityImport/InlineAssemblyShims.lean`), the importer replaces the block with that
entry's fixed lowering:

| Fingerprint constant | Block it selects (`Uniswap/v4-core` `46c6834`) | Fixed lowering |
| --- | --- | --- |
| `extsloadBatchYulFingerprint` | `Extsload.extsload(bytes32[] calldata)` | `lowerBatchArrayLoadShim`, one `sload` per key |
| `exttloadBatchYulFingerprint` | `Exttload.exttload(bytes32[] calldata)` | `lowerBatchArrayLoadShim`, one `tload` per key |
| `extsloadRangeYulFingerprint` | `Extsload.extsload(bytes32, uint256)` | `lowerBatchRangeSloadShim`, consecutive `sload`s |

A shortcut is selected only by the exact code fingerprint of the block, never by a function,
library, contract or variable name. The shortcut lowerings take a `TrustedShortcutMatch`, which
only a registry fingerprint match can build. `scripts/check_importer_name_selection.py` (in
`make check`) checks importer code (`Compiler/SolidityImport/`): a literal that is exactly a
name (wherever it is used), or a longer literal in a comparison or pattern, may only name a
Solidity or Yul builtin, a solc AST or JSON name, or one of the importer's own names; and no
fingerprint constant, fingerprint comparison or shortcut lowering may appear outside the
registry. It is a text check. Its exemptions (test-data literals in theorems and examples,
EmitVerity's printed names) and blind spots (names built at run time, a longer literal such as a
signature outside a comparison, selection by a function selector, a builtin or JSON name that
user code also gives its own declaration) are listed in the script and left to review. For a
replaced block the model is the fixed lowering, not a translation of the block, and no Lean
proof relates the two: each entry names the tests that compare the lowering's results with
solc's on the block (`TrustedShortcut.evidence`). A proof about a root whose model uses a
shortcut therefore says something about the deployed code only if the lowering and the block
agree, and that agreement is trusted (tested on the inputs those tests cover, not proved). The
import report lists the shortcuts each root's model uses, per function (`shortcut` lines under
its `status` line, see [Shortcuts used](#shortcuts-used)); a root without such a line uses none.

An address immutable that a constructor assigns `address(this)` is modeled as
the executing contract's address. That holds for code running at its own
address and not behind a `DELEGATECALL` (a proxy), where `address(this)` is the
caller of the delegate call. An inline `= address(this)` initializer is not
read that way: the synthesized constructor installs it. Other immutables are
explicit parameters, installed initializers, or values the source fixes.

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
scripts/check_solidity_differential.sh --programs 5 --cases 16 --seed 2438 --jobs 4 \
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
  `--shard I/N --jobs J` runs a deterministic share of the independent
  campaigns with `J` parallel isolated snapshots (`--jobs auto` sizes `J` by
  cores and available memory; `--task NAME` selects single campaigns); CI's
  `import-mutations` job runs 24 shards from the prepared `build` workspace.

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
A project may list optional `"exclude_functions"` (function names) in the
manifest; it is then reported both in full and as a milestone with only those
functions removed (Midnight currently excludes `multicall`). This is function-import coverage, not whole-contract ABI or EVM
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
| `=` and `op=` on scalar storage dynamic array, mapping, nested mapping, raw-slot struct member and struct-member mapping / dynamic array elements; whole-struct `=` to a mapping value or storage array element; `string` `=` to a mapping value (development; full release gates pending) | As solc (legacy and via-IR): evaluate and capture the RHS, then the mapping keys and index, then bounds-check and write; for `op=`, RHS, keys, current-value read, combine. Before, depending on the site, the keys ran first, so a reverting key and RHS raised the key's panic (`m[x - 1] = 10 / x` at x = 0: `Panic(0x11)`, solc `Panic(0x12)`), a key helper's storage write was visible to the RHS (`m[bump()] = stamp + 100`), an RHS helper's write moved the target slot (`m[stamp + k] = restamp()`), and a bare-local RHS was read after `i++` in the index (`arr[i++] += i`). The RHS is now bound to a fresh local before the key prelude. `push(v)` keeps solc's target-first order. Existing stateful-RHS and memory-order rejections stay. A struct value written to a (non-raw-slot) mapping value (constructor or helper call returning a memory struct, parenthesised or not, or a memory-typed conditional of those or of storage branches, which solc copies when the conditional runs, nested or not) has its member values captured before the keys (`held[i++] = Pair(i, i)`, `held[bump()] = viewPair()`); a storage struct variable, element or storage-pointer helper result is a reference whose members solc reads at the copy, after the target's keys, and the lowering reads them after the keys (`held[touch()] = held[0]`, `held[touch()] = heldZero()`). A `string` written to a mapping value or a storage `string`/`bytes` with a key prelude is built before the keys when it is a value (a literal, memory or calldata bytes, a call or an encoding: `labels[y - 1] = string(abi.encodePacked(10 / y))` at y = 0 raises `Panic(0x12)`, `labels[bump()] = string(abi.encodePacked(stamp))` stores the stamp from before the key helper); a storage source is copied after the keys, and a keyed storage source, whose own key solc evaluates before the target's, is a located rejection when that order is observable: the target's keys call or write (`labels[bump()] = labels[stamp]`), or the source can revert, call or write beside a target key prelude (`labels[x - 1] = labels[10 / x]`); an inert source (identifiers, literals, mapping lookups) imports (`labels[x + 1] = labels[x]`). A storage struct source (variable, element or storage-pointer helper result) copied into a mapping value or a raw-slot struct target (a storage array element) has its slot evaluated before the target's keys, with its own keys bound to fresh locals and its index checked, and its members read after them: `pairs[touch()] = pairs[0]` copies the members `touch` wrote, `held[j++ + 5] = held[j]` copies `held[0]`, `held[bump()] = heldAt(stamp % 3)` calls the helper before `bump`, and `pairs[y - 1] = pairs[10 / y]` raises the source's `Panic(0x12)`. A conditional that is not a value (a storage-typed conditional, `held[bump()] = c ? held[0] : held[1]`, or one with a memory or calldata variable branch, `held[bump()] = c ? p : Pair(stamp, 2)`) is a located rejection when the order is observable: solc evaluates its condition before the keys and copies the selected branch after them, which one lowering step cannot express. Observable means the target's keys call or write, or, for a mapping value target (where the lowering evaluates the conditional after the keys), the conditional can revert, call or write beside a target key prelude; `held[x + 1] = flag ? held[0] : held[1]` and `pairs[x % 2] = flag ? pairs[0] : pairs[1]` import. `MappingWriteOrderSequence`, `StructCopyWriteOrderSequence` (A/B/C; `check_storage_mutations` `import-assign-order-*`, `import-copy-order-*`; `check_storage_rejections` `struct-copy-storage-conditional-rejected`, `struct-copy-memory-variable-conditional-rejected`, `string-mapping-keyed-storage-source-rejected`, `string-mapping-reverting-key-storage-source-rejected`, `string-mapping-pure-key-storage-source-accepted`, `struct-copy-pure-key-conditional-accepted`). |

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
prerequisite does not implement CREATE2 code-deployment helpers: named returns, dynamic
byte construction and CREATE2 still require independent exact lowering and observations.
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
prerequisite for CREATE2 key-derivation helpers, not an implementation of code deployment.

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
| `super.fn(...)` helper calls | Verified against `referencedDeclaration == -25` (`type(contract super ...)`); resolved to the first implemented function in the same transitive `baseFunctions` family across the suffix of the target contract's `linearizedBaseContracts` strictly after the calling function's enclosing contract (matching `solc` C3 diamond `super` dispatch). ABI scalar argument checks follow this same suffix at each helper body: a forwarding `pure`/`view` override is not itself a cycle, but a reached custom or explicit revert is still rejected. See `EncodingArgSuperOverrideChecks` and `EncodingArgSuperOverrideSequence`. |
| Explicit base-qualified `Base.fn(...)` helper calls | Verified that `Base` is an identifier in the target contract's `linearizedBaseContracts` and that `fn` is declared in `Base`, then inlined statically without virtual dispatch. |
| Duplicate `storageLayout` labels (e.g. OpenZeppelin `private __gap`) | Unreferenced duplicate labels in `storageLayout.storage` do not block importing supported functions; any reference to a state variable whose label appears multiple times in `storageLayout.storage` fails closed with `shadowed storage declaration <name> is outside this slice`. |

### Development slice: void helpers, custom-error reverts, scalar booleans, and named root returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Zero-return internal, private, and internally-called public helpers | Lowered via continuation-passing (`lowerVoidHelperFrom`) so nested early `return;` inside `if`/`else` runs the post-conditional continuation only on fallthrough paths with restored lexical scope. |
| `revert CustomError(...)` (`RevertStatement`) | Lowered through `lowerErrorArguments` to `Stmt.requireError (.literal 0) name values`. |
| `bytes1`..`bytes31` custom-error parameters (`error LockedFunction(bytes4 selector)`) | Parameter types resolve through `localParamType` to `ParamType.bytesN n`. `Denote.customErrorScalarType` signs them `bytesN` in the selector, and `errorScalarValueValid` admits only left-aligned words (low `32 - n` bytes zero), matching the compiler's masked encoding. Argument restrictions are unchanged. Event parameters and `errorScalarType` are unaffected. Fixture: `CustomErrorFixedBytesSequence` (`check_storage --fixture custom-error-fixed-bytes`). |
| Scalar `bool` storage variables and prefix `!` | Stored as 8-bit packed storage with `logicalNot (logicalNot ...)` normalization on read and write; prefix `!` on `bool` lowers to `Expr.logicalNot`. |
| Named scalar root return parameters and empty-body scalar hooks | Root functions whose return parameters are all named scalars initialize each to zero and return them on bare `return;` or fallthrough; empty-body root or helper hooks return zero words. |

### Development slice: pre-placeholder modifiers, `unchecked` blocks, compound assignments, and scalar assignment expressions

| Supported Solidity | Lowering boundary |
| --- | --- |
| Pre-placeholder modifiers (`ModifierDefinition` / `ModifierInvocation`) | Modifiers whose body ends with a single trailing `_;` (`PlaceholderStatement`) and contains no earlier `_;`, no `return;`, and no `virtual` specifier are inlined in declaration order before root and helper bodies with their own lexical frame and `unchecked := false`. |
| `unchecked { ... }` (`UncheckedBlock`) | Enables wrapping unsigned arithmetic (`+`, `-`, `*` masked to `2 ^ bits - 1` when `bits < 256`) within the lexical block while preserving division/modulo-by-zero panic (`0x12`) and resetting `unchecked := false` across helper and modifier call boundaries. |
| Compound assignments (`+=`, `-=`) | Supported on declaration-bound unsigned scalar locals, unsigned scalar storage fields, unsigned scalar mappings, and unsigned mapping struct members, honoring checked vs `unchecked` arithmetic. |
| Narrow signed `+=`, `-=`, `++`, `--` (`int8`–`int248`) | `combineCompound`: both operands are cleaned (sign-extended) first, as solc does; a narrow signed local assigned in Yul can hold a dirty word. The raw word sum/difference is then exact; checked code keeps it only if it equals its own `signextend` and otherwise panics with `0x11`, `unchecked` code stores `signextend(raw)`. Other narrow signed compound operators reject. Admitted in every contract (formerly only with more than one state variable, and wrapping in checked code). `SignedCompoundAssignmentSequence` (fixture `signed-compound-assignment`) and `SignedStructCompoundSequence` (fixture `signed-struct-compound`, one state variable in the file: negative packed `int24` / `int8` / `int16` members of a storage struct array through an indexed element, a storage reference and a memory copy, the values of a postfix and a prefix increment, a narrower signed right-hand side, checked overflow at the range end and an unchecked wrap), both with variants `baseline` / `renamed` / `explicit`; mutants `import-signed-compound-operator` (`-=` lowered as `+=`), `import-signed-compound-overflow` (range check dropped), `import-signed-compound-unchecked` (no wrap in `unchecked`) and `import-signed-compound-extend` (operands not cleaned; the scalar fixture's Yul-assigned local is dirty). |
| Scalar assignment expressions (`(x = rhs)`) and constant `**` | Supported for `=` on declaration-bound scalar locals and scalar storage identifiers when any binary sibling operand is order-independent (`Literal` or constant) and call sites are single-argument; integer constant `a ** b` lowers when `a ^ b < 2 ^ 256`. |

### Development slice: multi-return helper inlining, tuple destructuring, parameter compound assignments, and narrow constant event arguments

| Supported Solidity | Lowering boundary |
| --- | --- |
| Multi-return internal, private, and internally-called public helpers | Unnamed multi-return scalar helpers (`returnParameters.parameters.size > 1`) allocate fresh `letVar` result bindings initialized to zero, evaluate and convert `Return` tuple components in source order into those bindings, and thread post-`if`/`else` continuations along fallthrough paths via `lowerVoidHelperFrom`. Named or reference return parameters and discarded multi-return calls remain rejected. |
| Tuple destructuring declarations and assignments (`(uint256 a, uint128 b) = fn(...)`, `(a, b) = fn(...)`, `(uint256 a, , uint128 c) = (x, y, z)`) | Supported when the RHS is a multi-return helper call of matching arity, or, for declarations only, a literal `TupleExpression` of matching arity whose components are evaluated left to right (including elided ones, so their panics and reverts keep solc's order) through the conditional-tuple leaf lowering before the fresh locals are bound; `VariableDeclarationStatement` requires at least one non-null declaration and binds declared components in order; `Assignment` (`=`) evaluates converted components into fresh temporaries and commits each non-elided target to a materialized scalar local or scalar storage field in order after rejecting duplicate local or storage targets. |
| Flat `memory` structs in multi-return helpers, tuple declarations and uninitialized locals (`returns (S memory p, uint256 k)`, `return (k, S(a, b))`, `(S memory p, uint256 k) = f(x)`, `S memory p;`) | A flat struct result binds one zero-initialized local per member (`inlineMultiFn`); a `return` tuple component of struct type evaluates its members in order into those locals (`lowerVoidHelperFrom`); a struct component of a tuple declaration takes one helper result per member, and every later component starts after them (formerly later components read from the component index, so `(S memory s, uint256 k, S memory t) = f(x)` bound `k` to `s`'s second member); `S memory p;` binds one zero local per member. All four lower the same way in every contract (formerly only with more than one state variable; `MemoryStructStateCountChecks`, #2830). Rejected with a location: one struct returned in two components of a `return` tuple (`return (t, 0, t)`, also through a conditional: the caller would get two aliases of one pointer), an elided struct component of more than one member (arity mismatch), a struct component of a literal tuple right-hand side, aliasing a destructured or uninitialized struct local (`q = p`), and uninitialized struct locals with a nested struct member. |
| Compound assignments (`+=`, `-=`) on unsigned scalar parameters | When an unsigned scalar parameter is modified by `+=` or `-=` in a root, helper, or modifier body (without direct `=` or `delete` parameter writes), the parameter is materialized into a declaration-bound mutable local copy at frame entry so call-by-value updates are visible within the frame without mutating caller bindings. |
| Narrow constant event arguments (e.g. `emit Initialized(type(uint8).max)`) | Canonical integer literals `Expr.literal n` with `n < 2 ^ bits` and empty prelude are accepted for `.uintN bits` event parameters in both `Import.lean` and `ValidationEvents.lean`, alongside direct matching `.uintN bits` parameters. |

### Development slice: `int256` arithmetic/storage/mappings and contract-typed scalar values

| Supported Solidity | Lowering boundary |
| --- | --- |
| `int256` / `int` scalar parameters, locals, returns, scalar storage fields, and scalar mapping values | Lowered as full 256-bit two's-complement words (`ParamType.int256` and `Word Int256` accessor bridge); narrow signed (`int8`..`int248`) locals and arithmetic keep sign-extended words (`signextend`), exercised for `%` by `SignedModuloSequence`; narrow signed mapping keys remain rejected. |
| `int256` prefix unary `-`, binary `+`, `-`, `*`, `/`, `%`, `<`, `>`, `<=`, `>=`, `==`, `!=`, and `+=` / `-=` / `%=` | Checked `+`, `-`, `*`, `/`, and unary `-` emit `Panic(0x11)` on two's-complement `int256` overflow (including `-type(int256).min`, `type(int256).min * -1`, and `type(int256).min / -1`) and `Panic(0x12)` on division by zero; `UncheckedBlock` switches signed `+`, `-`, `*`, `/`, `+=`, `-=`, and unary `-` to wrapping 256-bit two's-complement arithmetic while preserving division-by-zero `Panic(0x12)`. Signed comparisons use `slt` / `sgt` and signed division uses `sdiv`. Signed `%` and `%=` (`signedModulo`) use `smod`, the truncated remainder with the sign of the dividend (`(-7) % 4 == -3`, `7 % -4 == 3`), after the `Panic(0x12)` zero-divisor guard, which `UncheckedBlock` keeps; `type(int256).min % -1` is `0` and never panics. `SignedModuloSequence` (fixture `signed-modulo`) runs three equivalent variants A/B/C, the third rewriting every `a % b` except `min % -1` as `a - (a / b) * b`. |
| `type(int256).max`, `type(int256).min`, `type(uintN).min`, and `int256(x)` / `uint256(int256_x)` casts | `type(int256).max` lowers to `2^255 - 1`, `type(int256).min` to `2^255` (`-2^255` in two's complement), and `type(uintN).min` to `0`; explicit `int256(...)` and `uint256(...)` casts on 256-bit scalars and bounded constants preserve the 256-bit word representation. |
| Contract and interface scalar values (`contract Foo`, `address payable`) | Supported as 160-bit address-backed scalar parameters, locals, returns, scalar storage fields, scalar mapping values, and `ContractOrInterface(addr)` / `address(contractVal)` casts; external contract member calls fail closed with located diagnostics. |

### Development slice: internal function-pointer locals, mapping-struct `delete`, and post-placeholder modifiers

| Supported Solidity | Lowering boundary |
| --- | --- |
| Internal function-pointer local declarations (`function(...) internal ... ptr = f` or `cond ? f : g`) | Supported when initialized at declaration time to a direct internal/private helper identifier or a `Conditional` (`cond ? f : g`) whose branches resolve to internal/private helpers in the active contract hierarchy. For a conditional initializer, the condition is evaluated once at declaration and stored in a fresh boolean local; calling `ptr(args)` lowers to `lowerCall` on a direct target or a conditional dispatch evaluating arguments once in caller source order and branching on the stored condition to inline each target helper. Reassignment, uninitialized function-pointer locals, function-pointer parameters/returns/storage, and external function pointers fail closed with located diagnostics. |
| Whole-struct `delete` on mapping-backed structs (`delete m[k]`, `delete m[k1][k2]`) | Supported when the referenced struct has no `opaque` (nested mapping or dynamic array) members in `storageLayout` and every decoded member is an unpacked or packed scalar (`uint8`–`uint256`, `int256`, `address`, `bool`, `bytes32`). Keys are evaluated once into fresh temporaries if needed and each member is cleared to `0` in layout order. Structs with `opaque` or array members fail closed. |
| Modifiers with statements after `_;` (`ModifierDefinition` / `ModifierInvocation`) | Modifiers with a single top-level `_;` (`PlaceholderStatement`) may include both pre-placeholder and post-placeholder statements (for example `nonReentrant` guards). Multiple modifiers wrap outside-in around the body (`m1` outer, `m2` inner). On every non-reverting return or fallthrough path, return values are captured into fresh temporaries before running post-placeholder statements in the modifier's lexical frame. Modifiers with zero, multiple, or nested `_;` placeholders, `virtual` modifiers, and `return;` inside a modifier body fail closed. That includes a modifier whose body is one `if` around `_;` (`if (c) { _; }`), whatever the number of state variables: with more than one, the importer used to run the modified body unconditionally in roots and value helpers (#2830; `check_storage_rejections.py`, `conditional-modifier-*-rejected`). |

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
| Conditional tuple expressions (`cond ? (a0, ..., ak) : (b0, ..., bk)`) | Supported as the RHS of tuple variable declarations (`lowerLocal`) and tuple assignments (`lowerEffect`), including nested `Conditional` branches whose leaves are `TupleExpression`s or multi-return helper calls of matching arity. Target component types are threaded into each leaf so integer constants (such as `0 days`, `1 days`) convert to the declared component type before branch joining via fresh temporaries and `Stmt.ite`. Stateful or assignment expressions inside tuple components fail closed, as do bare top-level `TupleExpression` RHSs of tuple assignments. |
| Transient storage `tload(slot)` in single-assignment `InlineAssembly` | `lowerYul` lowers `tload(a)` to `Expr.tload`, covered by `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses` (evaluating `DenoteState.transientStorage`). `tstore` and multi-statement assembly blocks remain outside this slice. |

### Development slice: fixed-size unsigned scalar array members in mapping structs and root fixed-size array returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Fixed-size unsigned scalar array members inside mapping structs (`struct S { ... uintN[L] arr; }`) | Decoded from `storageLayout` when the array member has `encoding == "inplace"`, `byteOffset == 0`, positive length `L`, and unsigned scalar elements (`uint8`–`uint256`). Expanded on demand (`usedStructFixedArrays`) into packed or full-word `StructMember` entries `__solidity_struct_array_{member}_{index}` at `wordOffset + index / perWord` only in slices that access the array member; unreferenced array members remain listed in `report.opaqueMembers`. Element reads, writes, `delete`, and memory snapshot copies (`uintN[L] memory snap = m[k].arr;`) enforce dynamic bounds checks (`Panic(0x32)`). Whole-struct `delete m[k]` and whole-array `delete m[k].arr` fail closed. |
| Unnamed root fixed-size scalar array returns (`returns (T[L] memory)`) | Supported when a root function declares a single unnamed `T[L] memory` return parameter with supported scalar element type `T` and positive length `L`. Lowered as `L` consecutive ABI return words (`Array.replicate L elemPty`); `Return` statements accept either an inline array literal `[e_0, ..., e_{L-1}]` (converting each pure/stateless component to `T` in order) or a local fixed-size array snapshot identifier of matching type and length. Fixed-size memory array values (locals, parameters, helper results) also return their `L` words (see the fixed-size memory array slice). Named `T[L] memory` root return parameters, stateful inline array components, and other return expressions fail closed. |

### Development slice: fixed-size memory arrays (`T[N] memory`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `T[N] memory` locals, internal helper parameters and internal helper results (`T` a scalar accepted by `scalarArrayElement?` except `bytes4`, `N > 0`) | A `T[N] memory` value is a pointer to `N` consecutive words without a length word (`Env.fixedMemArrays`, `FixedMemArray`). `T[N] memory x;` allocates `N` zeroed words at the free memory pointer (`allocateZeroedFixedMemArray`, with solc's `Panic(0x41)` allocation guard); `T[N] memory x = e;`, `x = e;`, helper arguments and helper results bind `e`'s pointer and never copy, so writes through a helper parameter are visible to the caller. Helper results are allocated and zeroed on entry, named or unnamed, as solc does; `return e` stores `e`'s pointer into the result (`inlineFixedArrayFn`, general control flow through `lowerVoidHelperFrom`). `delete x` binds a fresh zeroed array. |
| Element reads, writes, `delete x[i]`, compound assignments `x[i] op= v`, and `x.length` | Element `i` lives at `pointer + 32 * i`. A constant in-range index has no runtime guard; a runtime index is guarded by `lt(i, N)` and `Panic(0x32)`. Writes evaluate the right-hand side before the index; compound assignments read the element after both. `x.length` is the constant `N`. Narrow unsigned elements are written already in range and `bool` elements are normalized. |
| Root `T[N] memory` parameters and `return x` of a `T[N] memory` value from a root returning `T[N] memory` | A root with a `T[N] memory` parameter uses the explicit ABI prelude (`ExternalAbiDecoding.explicitPrelude`): solc's static-head size check (`calldatasize < 4 + head` reverts with empty data), per-element canonicality checks (`uintN` / `address` / `bool` upper bits revert with empty data), then an eager copy of the `N` words to memory. A root returning `T[N] memory` returns the `N` words of any fixed-size memory array value. |
| Inline array literals `[e_0, ..., e_{N-1}]` as values (`T[N] memory t = [...]`, `t = [...]`, helper arguments, helper `return [...]`) | Lowered by `lowerInlineArrayLiteral`: solc's `allocate_memory_array` reserves the `N` words (no zeroing), then each component is evaluated left to right, converted to the literal's common element type `T` (`uint8[3]` for `[1, 2, 3]`) and stored at `pointer + 32 * i`. The result is an ordinary `T[N] memory` value: indexed at runtime with the `Panic(0x32)` guard, writable, passed by reference. Directly indexed constant literals keep the inline constant array slice; stateful or assignment components of multi-element literals reject. |
| Rejected | `T[N] calldata` and `T[N] storage` parameters (`unsupported location ...`), copies from calldata, nested and multi-dimensional fixed arrays, `bytes4[N]`, array-valued conditionals, `++` / `--` on elements, and fixed-size memory arrays inside ABI encoding, hashing or events keep failing with located diagnostics. |

`FixedMemoryArraySequence` (fixture `fixed-memory-arrays`, variants `baseline` / `renamed` / `unrolled`) exercises by-reference helper writes, named and unnamed helper results, the aliasing `return st`, dynamic and constant indices, `uint8[3]`, compound assignments, an out-of-range `Panic(0x32)`, and the root `rotateFixed(uint256[4],uint64[2])` with canonical, dirty, overflowing and truncated heads. Its `rebind` helper covers `delete x`, `delete x[i]`, `x = y`, `T[N] memory y = x`, a helper rebinding its own parameter (the caller's array is unchanged), an array declared in a loop body (zeroed each iteration), nested scalar and array helpers, `bool[2]` / `address[2]` / `int256[2]`, and `x[x[1]] = f(x)` (right-hand side before index). Mutants: `import-fixed-memory-array-reference` (copy instead of reference), `-offset`, `-bound`, `-return`, `-zero` (fresh arrays not zeroed), `-free-pointer` (no free-pointer bump), `-write-order` (index before right-hand side).

**Memory-writing helpers and evaluation order.** `T[N] memory`, `T[] memory`, `bytes`/`string memory` and memory structs reach internal helpers by reference, so a `pure` or `view` helper can write memory a sibling expression reads, which `statefulCallIn` does not see. `memoryWriteIn` flags an internal call with a by-reference memory argument or receiver whose callee (transitively) assigns, deletes or increments through a memory reference, writes memory in inline assembly (`mstore`, the `*copy` family, calls returning into memory), or has modifiers; `memoryWriteOrderHazard` fires when one sibling may write and the other reads a memory reference. Binary operands with such a hazard are rejected (`memory-writing helper operands require explicit evaluation-order support`): solc evaluates them right-to-left on the legacy pipeline and left-to-right under via-IR. Assignments and compound assignments whose storage target captures a mapping key or array index before the right-hand side (scalar mappings, storage dynamic arrays, struct-mapping and member paths) are rejected the same way, because solc evaluates the right-hand side first on both pipelines; paths that already evaluate the right-hand side first (memory array elements, storage fixed-array elements, raw-slot members, and compound writes to dynamic arrays and struct mappings) are unchanged. Positional scalar arguments of a direct internal helper are evaluated left to right on both solc 0.8.34 pipelines. For scalar identifier updates (`x++`, `++x`, `x = y` or a literal), the importer captures each argument before the next write. A non-view helper that only returns a storage path can supply an argument or a library receiver alongside simple scalar bindings. A receiver is evaluated **after** its arguments on legacy and **before** them on via-IR; competing receiver effects, assignment calls through function pointers, and assignments beside composite arguments (including implicit storage-to-memory copies) keep their located rejection. This also closes the same divergence for `T[] memory` and memory-struct helper parameters, which predates fixed-size memory arrays.

`InlineArrayLiteralSequence` (fixture `inline-array-literals`, variants `baseline` / `renamed` / `element-writes`) reads a constant 32-bit-field table bound to a local inside a loop through an inlined helper (`(t[k >> 1] >> (32 * (k & 1))) & 0xffffffff`), a literal with runtime components, a `uint8[3]` literal, literal reassignment, a literal helper argument read out of range (`Panic(0x32)`), and a literal in `fail()`. Mutants: `import-inline-array-literal-order` (elements stored in reverse) and `import-inline-array-literal-allocation` (one word too few reserved).

### Development slice: dynamic memory arrays through internal functions (`T[] memory`, `T[][] memory`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| Internal helpers returning `T[] memory` with control flow (loops, branches, early `return`) and named results (`returns (T[] memory c)`) | `inlineArrayFnGeneral` (selected when the result is named or the body is not straight-line; straight-line unnamed helpers keep `lowerArrayHelperStmts`). The result variable starts as solc's zero value, the zero-length array at `0x60`; a named result binds it, `c = e` and `return e` store `e`'s pointer and length. The caller binds the returned pointer: no copy. |
| `T[] memory` results inside multi-return helpers (`returns (T[] memory head, uint256 total)`), and `T[N] memory` results there | Each array result is a pointer word in `multiHelperResults` (dynamic results start at `0x60`, fixed results are allocated and zeroed); tuple `return (a, b)` snapshots each pointer; `(T[] memory a, uint256 t) = f(...)` binds the pointer and reads the length from the header. |
| `string memory` / `bytes memory` results among several helper results (`returns (string memory, string memory)`, `returns (bool ok, bytes memory data)`), bound by `(string memory n, string memory v) = f()` or `(name, version) = f()` (#2844) | `inlineMultiFn` gives each such result its own pointer and length bindings, one buffer per tuple position, starting as solc's empty buffer, in two `multiHelperResults` slots (pointer, then size). A named result is a rebindable buffer like a named root string or bytes result; `return (e0, e1)` captures each buffer component's pointer and size in component order; `return g(...)` forwards another helper's slots after checking their types. A tuple declaration binds each component like a single `string` / `bytes` helper result (`lowerLocal`); a tuple assignment rebinds a writable named result or non-literal `bytes` local. Only the pointer is copied, as in solc: a helper returning one buffer twice gives two aliases, and a returned parameter aliases the caller's buffer, so the caller's later element write through its own `new bytes` local shows through the result (solc 0.8.34, legacy and via-IR). Fail closed with a location: element writes through a tuple-bound buffer local, an elided string/bytes component, tuple-literal or conditional initializers and conditional tuple-literal returns with string/bytes components, tuple assignment to a `new bytes` local, to a storage string or bytes target, to one buffer local twice, or from `abi.decode`. `MultiReturnBufferSequence` (A/B/C, `multi-return-buffers`; mutants `import-multi-return-buffer-*`) runs (bool, bytes) results of length 0, 31, 32, 33, 40 and a reverting helper, unnamed and named (string, string) results, both aliasing shapes, a storage-derived buffer before a later storage write, a tuple assignment and a forwarded helper. |
| Reassignable `T[] memory` locals and parameters (`T[] memory d;`, `d = c;`, `delete d;`, reassigned helper parameters) | `ScalarArrayParam.reassignable` descriptors own mutable pointer/length bindings (`ownDynArray`); assignment rebinds both, `delete` rebinds `0x60`. A helper parameter that the body reassigns or deletes owns its bindings, so the caller's variable is unchanged while memory stays shared. Any other `T[] memory` parameter bound to a reassignable caller variable snapshots its pointer and length at the call, so a helper result that returns the parameter (`return p`), or a Yul `res := p` cast, keeps the array as passed when the caller later rebinds its variable; element writes through either name still reach the same memory. Element compound assignments `a[i] op= v` evaluate the right-hand side, then the index and its `Panic(0x32)` check, then read the element. |
| `T[][] memory` locals, element access and helper parameters | `NestedMemArray` (`Env.nestedMemArrays`): `new T[][](k)` allocates `k + 1` words with solc's `Panic(0x41)` guards and points every element at `0x60` (solc's `zero_complex_memory_array`). `v[i]` checks `i < v.length` (`Panic(0x32)`) and loads the inner pointer, an ordinary `T[] memory` value (`v[i][j]`, `v[i].length`, `T[] memory row = v[i]`, passing `v[i]` to a `T[] memory` parameter); `v[i] = a` stores `a`'s pointer, `v[i][j] = x` writes through it after both bounds checks. `T[][] memory` helper parameters share the outer array. |
| Rejected | Internal helpers returning `T[][] memory` (`nested memory array helper results are outside this slice`, or the existing helper-result diagnostics), root `T[][]` parameters (`unsupported parameter type uint256[][]`) and returns, `T[][]` in ABI decoding, encoding, hashing and events, deeper nesting (`T[][][]`), arrays as memory struct members and struct-valued helper results, calldata-to-memory array assignment (`calldata-to-memory array assignment is outside this slice`), `v[i][j]` with an index that needs a prelude, a `for` loop bound `a.length` / `v.length` whose array the loop body rebinds (`a = b`, `delete a`, `v = new T[][](k)`; solc re-reads the length on every test: `a for loop bound must be a literal, a parameter or an unassigned local`), and Yul inside a helper that names an array result or tuple-declared array (`unbound Yul identifier`, rather than resolving a same-named caller array). |

`DynamicMemoryArraySequence` (fixture `dynamic-memory-arrays`, variants `baseline` / `renamed` / `explicit`) exercises a named result built in a loop (`add`), an unnamed result with an early aliasing return (`scaled`), a multi-return with a named array result (`split`), a multi-return `return (a, a.length)` / `return (w, k * 7)` with an unnamed array result (`window`), by-reference writes through a parameter (`bumpAll`), a zero-value local reassigned conditionally, a `uint256[][]` whose rows are a local and a helper result, a nested-array helper parameter (`vecSum`), an untouched `0x60` row, out-of-range `Panic(0x32)` reads and writes, helper parameters that are returned (`same`), deleted (`clear`) and reassigned (`rebind`, `a = b` then `a = new …`) while the caller keeps reading its own array, a `uint8[]` element `op=` overflow (`Panic(0x11)`), an out-of-range element `op=`, a `bool[]`, and a `uint256[][]` whose rows alias (`m[0] = m[1]`) before `delete m[1]` / `delete m`. Mutants: `import-dynamic-memory-array-result`, `-reassign`, `-multi`, `-nested-zero`, `-param-snapshot`, `-param-owner`, `-compound-bound`.

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
| Extended compound assignments (`<<=`, `>>=`, `&=`, `|=`, `^=`, `/=`, `%=`) | Supported across declaration-bound scalar locals, writable helper/modifier parameters (`bodyCompoundAssignedIds`), scalar storage fields, scalar mappings, and unsigned mapping-struct members: `<<=`, `>>=`, `&=`, `|=`, `^=`, `/=`, `%=` on `uintN`; `/=`, `%=`, `<<=`, `>>=`, `&=`, `|=`, `^=` on `int256`; and `&=`, `|=`, `^=` on `bytes32`. |
| Single-assignment Yul arithmetic, comparison, and bitwise builtins (`sub`, `div`, `mod`, `and`, `or`, `shl`, `shr`, `sar`, `gt`, `eq`, `iszero`, `not`) | Extended `lowerYul` in the single-assignment inline assembly subset (such as `UtilsLib.zeroFloorSub`), lowering directly to the corresponding `Expr` constructors covered by `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses`. |

### Development slice: bounded `while` loops, Yul `clz`, struct local declarations, and `calldata`-to-`memory` struct conversions

| Supported Solidity | Lowering boundary |
| --- | --- |
| Bounded unsigned `while` loops (`WhileStatement`) and `--counter` / `counter -= 1` in `for` loop headers | `lowerWhile` supports `while (v != 0)` / `while (v > 0)` (and `0 != v` / `0 < v`) on a writable unsigned `uintN` local `v` (`bits ≤ 256`) when the body contains no `return`, does not assign `v` before the final statement, and ends with a strictly decreasing bit-clearing or right-shift update: (1) positive constant right shift (`v >>= k` or `v = v >> k`, `1 <= k < 256`), (2) lowest-set-bit clear (`v &= v - 1` or `v = v & (v - 1)`), or (3) MSB bit clear (`uintM b = msb(v); ...; v &= ~(1 << b)` or `v = v.clearBit(b)` where `msb` computes `sub(255, clz(x))` and `b` is not reassigned). Lowered to `Stmt.forEach loopVar (.literal bits) [.ite condVal.expr bodyOut.toList []]`, which executes at most `bits` guarded iterations. A `while (!cond)` loop gives no derivable iteration bound and is a located rejection in every contract (`WhileNegatedConditionChecks`); it used to lower to at most 256 guarded iterations when the sources declared more than one state variable, silently cutting longer loops short. `lowerFor` also accepts `--i` and `i -= 1` as `for` loop step expressions so `bodyAssignedIds` detects any counter mutation in loop bodies. |
| Dividing unsigned `while` loops (development; full release gates pending) | `lowerDivisionWhile?` admits `while (v > X)`, `while (X < v)` and `while (v != 0)` on a writable unsigned `uintN` local `v` whose body has exactly one top-level `v /= k` or `v = v / k` (literal `k ≥ 2`, through narrowing casts no narrower than `v`), no other write to `v`, and no `break`, `continue` or `return`; the step may sit anywhere in the body and other statements may revert. `X` is any side-effect-free unsigned operand. Each iteration whose condition holds at least halves `v`, so `v` is `0` after `bits` of them and the condition is then false for every `X`; a failed condition changes nothing. Lowered to `bits` guarded iterations, as above. `DividingWhileSequence` runs A/B/C up to 246 iterations. |
| Yul `clz(x)` in single-assignment `InlineAssembly` | `lowerYul` lowers `clz(a)` (EIP-7939 Count Leading Zeros, 256 for `0`) into an unrolled 8-step binary search over `[128, 64, 32, 16, 8, 4, 2, 1]` using `Expr.shr` and `Stmt.ite`, producing a pure `Denote`- and `Yul`-compatible statement prelude without requiring custom EVM opcodes in downstream proofs. |
| `memory` and `calldata` struct local declarations (`Struct memory s = ...`, `Struct calldata s = ...`) and `calldata`-to-`memory` helper argument conversions | `lowerLocal` supports non-reassigned `memory` and `calldata` struct locals initialized from a root/helper struct reference (`.mem`) or a struct-array element (`m.tranches[i]`, `.abiElement`). Initializing a `memory` struct local or `memory` helper parameter from a `calldata` struct or `calldata` struct-array element materializes the struct into freshly allocated memory (`AbiRootLowering.materializeFromCalldata` / `AbiRootLowering.materializeElementFromCalldata`), validating scalar bounds and array heads at copy time; `memory`-to-`calldata` conversions and reassigned struct locals fail closed with located diagnostics. Referenced `immutable` state variables of value types are supported (see the immutables row above); enum and function-typed immutables, and immutables whose inline initializer is not a deployment-environment expression, fail closed with `immutable state variable <name> is outside this slice`. |

### Development slice: `abi.encodeWithSelector`, `.selector` byte buffers, Yul arithmetic/bitwise/context builtins, and external/ABI rejection diagnostics

| Supported Solidity | Lowering boundary |
| --- | --- |
| `<typeOrLocalOrThis>.<fn>.selector` in `abi.encodeWithSelector` and `abi.encodePacked` | `lowerSelectorBytes` resolves the referenced function or public state-variable getter declaration's 8-character `"functionSelector"` hex string and allocates a 4-byte memory buffer containing the left-aligned 32-bit selector word (`word * 16^56`, `size := 4`). `isPureSelectorReceiver` requires the receiver to be a contract/interface/library type (`type(contract ...)`), `this`, a literal, or a local/parameter variable (including `Contract(x)` casts around them); storage-variable receivers fail closed (`selector receiver must be a contract/interface type, this, or a local/parameter`) because unoptimized vs via-IR optimized `solc` differ on whether evaluating `stateVar.fn.selector` emits an `SLOAD`. Standalone `.selector` expressions outside `abi.encodeWithSelector` / `abi.encodePacked` fail closed. |
| `abi.encodeWithSelector(selector, args...)` as an encoded byte buffer (`keccak256(...)`, `bytes memory` locals, `abi.encodePacked(...)`) | Lowered by `lowerEncodedBytes`: for zero payload arguments, returns the 4-byte `lowerSelectorBytes` buffer directly; for one or more scalar arguments, validates and lowers each argument in order (`checkEncodingScalar`), stores their 32-byte words via `AbiEncoding.staticWords`, and concatenates the 4-byte selector prefix and `32 * n`-byte argument payload into a freshly allocated `(4 + 32 * n)`-byte buffer via `AbiEncoding.packedBuffer` and `AbiEncoding.copyBytes`. Non-byte-buffer uses of `abi.encodeWithSelector` fail closed with `abi.encodeWithSelector is only supported as a byte buffer`. |
| Extended Yul arithmetic, bitwise, comparison, and context builtins (`sdiv`, `smod`, `exp`, `byte`, `signextend`, `slt`, `sgt`, `caller`, `address`, `timestamp`, `number`, `chainid`) | `lowerYul` validates builtin name and arity before lowering arguments (`unsupported Yul builtin <fname>`), and lowers `sdiv`, `smod`, `byte`, `signextend`, `slt`, `sgt`, `caller`, `address`, `timestamp`, `number`, and `chainid` to their exact `Expr` counterparts (and `exp(a, b)` to `Expr.externalCall "exp" [a, b]`). `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses` include `.smod`, `.byte`, and `.signextend` with reflexive `rfl` arm-pin lemmas `evalExpr_smod_arm`, `evalExpr_byte_arm`, and `evalExpr_signextend_arm`. |
| Located diagnostic for multi-word external call results | A contract-typed call whose callee returns more than one word (`(a, b) = C(addr).f()`) fails closed with `external contract calls are outside this slice`, whatever the number of state variables. It used to lower, whenever the compiled sources declared more than one state variable in total (in any contract), as two `staticcall`s that each decoded word 0 (so the second result equalled the first), without checking that `f` is `view`. The bare statement `C(addr).f();` and partial destructuring `(a, ) = C(addr).f()` reject the same way. `ExternalTupleCallChecks` pins the rejection for a 2-variable and a 1-variable caller and for both other forms. Not external calls: `(a, b) = super.f()` and `(a, b) = Base.f()` for an internal base-contract `f` are inlined like any internal call. Before, they were rejected with `external call is missing functionSelector` whenever the sources declared more than one state variable. `ExternalTupleCallChecks` imports them in `InternalTupleBaseCall`. |
| Located diagnostics for `<addr>.code`, `abi.decode`, and low-level calls / `FunctionCallOptions` | `<addr>.code` fails closed with `external contract code reads are outside this slice`; `abi.decode(...)` fails closed with `abi.decode is outside this slice`; and `<addr>.call`/`staticcall`/`delegatecall`/`transfer`/`send` and `fn{value: ...}(...)` (`FunctionCallOptions`) fail closed with `external contract calls are outside this slice`. |

### Development slice: dynamic scalar-array and string parameters, string locals/helpers, and `selfbalance` / `tx.origin` context reads

| Supported Solidity | Lowering boundary |
| --- | --- |
| Root and helper `T[] calldata` / `T[] memory` scalar array parameters (`uint8`–`uint256`, `int256`, `address`, `bool`, `bytes32`) | Root `T[] calldata` parameters validate the ABI head, `uint64` length bound, and `32 * length` payload tail via `AbiLowering.scalarArrayCalldataHead`; root `T[] memory` parameters materialize and validate every element word via `AbiLowering.scalarArrayMemoryHead`. A `calldata`-to-`memory` copy (a `T[] memory` helper argument, `AbiLowering.materializeCalldataScalarArray`, or a `T[] memory` root result, `lowerDynamicTupleReturn`) validates each element on via-IR and cleans it on the legacy pipeline (`AbiLowering.legacyCleanScalar`: masked `uintN` / `address`, `bool` as `iszero(iszero(x))`, `bytes4` low bytes cleared), as solc 0.8.34 does (`CalldataNarrowArrayCopyChecks`, suite checks `calldata-narrow-array-copy` and `calldata-narrow-array-copy-solc0810`). Legacy ABI coder v1 (`pragma abicoder v1`, or solc 0.7.6 without `pragma abicoder v2`) copies the words raw, so there a narrow-element copy is rejected (`narrow calldata array copied to memory under ABI coder v1 is outside this slice`). Other ABI coder v1 differences on solc 0.8.x (raw `abi.encode` / event data, cleaned scalar parameters) are not modeled: such sources are imported as ABI coder v2. Supports `arr.length`, `arr[i]` (with `Panic(0x32)` bounds check and calldata element validation via `AbiLowering.readScalarArrayElement`), `for (uint256 i = 0; i < arr.length; i++)`, and internal helper forwarding. Nested arrays, narrow signed element arrays (`int8[]`–`int248[]`), `string[]`, `bytes[]` helper parameters, and array element writes fail closed (root `bytes[]` and `S[]` parameters: see the root ABI parameter slice below). |
| Root and helper `string calldata` / `string memory` parameters, `string memory` locals, `bytes(s)` / `string(b)`, and `bytes(s).length` | Root `string calldata` and `string memory` parameters decode via `AbiLowering.bytesCalldataHead` and `AbiLowering.bytesMemoryHead` (`ParamType.string`). Non-reassigned `string memory` locals and `string memory` helper parameters lower to retained `(pointer, size)` byte buffers (`stringBuffers`), supporting string literals, `string(abi.encodePacked(...))`, and single-return `string memory` helpers (`inlineStringFn`). `bytes(s).length` lowers to the buffer's byte length, and `s` / `bytes(s)` can be hashed (`keccak256`) or concatenated in `abi.encodePacked(...)`. Reassigned `string` locals fail closed. |
| `address(this).balance`, `payable(address(this)).balance`, `tx.origin`, and Yul `selfbalance()` / `origin()` | `address(this).balance`, `payable(address(this)).balance`, and Yul `selfbalance()` lower to `Expr.selfBalance`; `tx.origin` (`referencedDeclaration == -15`, `t_magic_transaction`) and Yul `origin()` lower to `Expr.txOrigin`. Covered by `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses` with reflexive `rfl` arm-pin lemmas `evalExpr_selfBalance_arm` and `evalExpr_txOrigin_arm`. External account `<addr>.balance` reads (`external account balance reads are outside this slice`) and `tx.gasprice` (`unsupported transaction context member gasprice`) fail closed. |

### Development slice: `bytes memory` parameters/locals/helpers, `.length` on byte buffers, `bytes.concat` / `string.concat`, `abi.encodeWithSignature`, and `abi.encodeCall`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Root and helper `bytes memory` parameters, `bytes calldata`-to-`bytes memory` copies, and single-return `bytes memory` helpers | Root `bytes memory` parameters decode and materialize calldata into memory at entry via `AbiLowering.bytesMemoryHead`, registering a retained `(pointer, size)` buffer in `byteBuffers` (`pointer := memoryPointer + 32`, `size := lengthBinding`). Initializing a `bytes memory` local or `bytes memory` helper parameter from a `bytes calldata` parameter copies the calldata words into freshly allocated memory via `AbiEncoding.reserve` and `Stmt.forEach`; passing a string literal (`literal_string`) or `bytes memory` buffer to a `bytes memory` helper parameter binds its `(pointer, size)` descriptor in the callee frame; and single-return internal/private/public `bytes memory` helpers inline via `inlineStringFn` (including expression-statement calls whose side-effect prelude is preserved). Reassigning a `bytes memory` local is the named-return slice below. |
| `.length` on `bytes memory` locals/parameters and inline encoded byte-buffer expressions | `lowerMember` lowers `<expr>.length` on any `bytes` / `bytes memory` / `bytes calldata` expression (`byteBuffers`, `calldataBytes`, `bytes(s)`, `bytes.concat(...)`, `abi.encode(...)`, `abi.encodePacked(...)`, `abi.encodeWithSelector(...)`, `abi.encodeWithSignature(...)`, `abi.encodeCall(...)`, and `bytes memory` helper calls) to `{ pre := buf.pre, expr := buf.size }`. Direct `.length` on `string` without `bytes(...)` conversion remains rejected by `solc`. |
| `bytes.concat(...)` and `string.concat(...)` builtins | Verified as `ElementaryTypeNameExpression` (`bytes` or `string`) `.concat` calls with `referencedDeclaration == none`. `bytes.concat` accepts `bytes`, `bytes memory`, `bytes calldata`, `bytes32`, `bytes4`, and `literal_string` arguments; `string.concat` accepts `string`, `string memory`, `string calldata`, and `literal_string` arguments. Both lower via `lowerPacked` (evaluating arguments right-to-left to match `solc --via-ir`, allocating a zero-padded output buffer via `AbiEncoding.packedBuffer`, and copying each argument's exact byte length via `AbiEncoding.copyBytes`). Non-byte-buffer uses of `bytes.concat` / `string.concat` and unsupported argument types (such as `uint256`) fail closed with located diagnostics. |
| `abi.encodeWithSignature(sig, args...)` and `abi.encodeCall(ContractOrInterface.fn, (...))` as encoded byte buffers | `abi.encodeWithSignature` lowers `sig` (`string` or string literal) as a byte buffer, computes the 4-byte selector word `keccak256(sigPtr, sigSize) & (0xffffffff * 16^56)` into a 4-byte buffer, validates and lowers each scalar payload argument (`checkEncodingScalar`), and concatenates selector + `32 * n` argument words via `encodeSelectorAndWords`. `abi.encodeCall` resolves the target `ContractOrInterface.fn` `FunctionDefinition` and its 8-hex-char `"functionSelector"` via `lowerMemberFunctionSelector` (requiring a pure contract/interface/library type, `this`, literal, or local/parameter receiver), checks that the second argument's tuple component count matches the target declaration's parameter count, converts each scalar argument to its declared parameter type via `convert pty argTy` (rejecting out-of-range narrow unsigned integer literals), and concatenates the 4-byte selector and `32 * n` words via `encodeSelectorAndWords`. A target with a `bytes` parameter beside scalar parameters is encoded as solc does, the selector followed by `abi.encode` of the arguments against the declared parameter types (`lowerAbiEncodeArgs`: static heads, an offset per `bytes`, then its length and zero-padded data; `prefixSelector`), for literal, memory, calldata, storage and helper `bytes` arguments; any other non-scalar parameter beside a `bytes` parameter (struct, array, `string`, `bytesN` other than `bytes1` / `bytes4` / `bytes32`, function type) fails closed at its argument. The `bytes` route itself does not depend on the state-variable count (formerly two raw words, the memory pointer and size, with more than one state variable; `EncodeCallBytesStateCountChecks`, #2830); scalar siblings keep the `checkEncodingScalar` rules of `abi.encode`, whose binary-operation and conditional admission still depends on it (#2830). An external call returning `bytes` / `string` (`token.name()`) used as a byte buffer is rejected at the callee for every state-variable count (it needs dynamic return decoding). Non-byte-buffer uses and non-scalar payload types fail closed. |

### Development slice: unnamed root dynamic `bytes` and `string` returns (`Stmt.returnBytes`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| Unnamed root `returns (bytes memory)` / `returns (bytes calldata)` and `returns (string memory)` / `returns (string calldata)` | Supported when a root function declares a single unnamed `bytes` or `string` return parameter (`functionDynamicBytesReturn?`) and each reached root `Return` expression satisfies `canLowerDynamicBytesReturnExpr`: string/hex literals, root `bytes` / `string` parameters (`calldata` or `memory`), constant `bytes` / `string` state variables, `bytes(...)` / `string(...)` conversions, `string.concat(...)`, `abi.encode(...)`, `abi.encodePacked(...)`, `abi.encodeCall(...)`, or single-return internal/private/public `bytes memory` / `string memory` helper calls (`_concat`, etc.). Lowers the return expression via `lowerEncodedBytes` into a fresh `_verity_memret_<stem>` pair (`_data_offset := buf.pointer`, `_length := buf.size`), runs any modifier post-placeholder statements (`env.rootPost`), and emits `Stmt.returnBytes "_verity_memret_<stem>"`. `Denote.returnBytesWords` and `Compile.compileStmt` read 32-byte words from memory when `name.startsWith "_verity_memret_"` and right-zero-pad the final partial word (`32 :: length :: paddedWords`), covered by `Coverage.stmtCovered`, `Quote.quoteStmt`, and `TransactionAccess.statementAccesses` with reflexive `rfl` arm-pin lemma `execStmt_returnBytes_arm`. A named `bytes` or `string memory` root return is the slice below; named `string calldata` root returns, missing root returns, and parameter names starting with `_verity_memret_` fail closed with located diagnostics. |

### Development slice: named `bytes memory` returns, calldata slices as helper arguments, and memory structs with `bytes` members

| Supported Solidity | Lowering boundary |
| --- | --- |
| Named `returns (bytes memory out)` of roots and inlined helpers, and named `returns (string memory out)` of roots | A root's named `string memory` result (`functionDynamicBytesReturn?`) binds the same buffer as a named `bytes` result, since both share the length-prefixed memory layout and ABI encoding: `out = "literal"`, `out = <string memory value>`, `out = <string calldata value>` and `out = <storage string>` rebind it, copying a literal, calldata or storage source into memory and aliasing a memory value, as solc's pointer assignment does. The name binds an empty buffer (pointer `0x60`, length 0) before the body. `out = <buffer>` and `out = abi.encodePacked(...)` rebind the `(pointer, size)` pair of a writable `bytes memory` local (a named result, or a local not bound to a literal), copying a `bytes calldata` value or slice into memory as solc does; `return <buffer>` stores into the same pair (`inlineNamedBytesFn`, `namedBytesResultMarker`). A root returns the bound buffer on fallthrough through `Stmt.returnBytes`. Solidity rejects a bare `return;` in a function with return parameters, so `return out;` is the early exit. The same rebinding applies to a reassigned `bytes memory` parameter: a parameter bound from calldata gets a fresh copy with its own length binding, so `p = ...` in the callee leaves the caller's calldata length and contents unchanged. Named `string` results of inlined helpers, named `string calldata` root results, element writes to a named result (`out[i] = ...`), inline assembly in such a helper, and returns inside its loops fail closed. |
| `bytes calldata` slices `data[a:b]` / `data[a:]` / `data[:b]` as internal helper arguments | `lowerCallArgs` lowers the slice with solc's checks `start <= end` and `end <= length`, which solc 0.8.34 emits as plain `revert(0, 0)` (`calldata_array_index_range_access`), not `Panic(0x32)`. A `bytes calldata` parameter binds the `(offset, length)` pair; a `bytes memory` parameter copies it into memory. A slice of a memory-backed `bytes calldata` value (a conditional `c ? a : b` argument) is copied into a fresh buffer as well, since solc's slice stays in calldata and shares nothing with the source. Such a call nested inside an `abi.encodePacked` / `abi.encode` argument keeps the existing `effectful ABI encoding argument` rejection, since the range check can revert; bind its result to a local first. |
| Memory structs whose members are ABI scalars and at least one `bytes` member: `S({a: data[0:48], ...})`, helpers `returns (S memory)`, locals, member reads, and struct arguments | Solc's memory layout: a struct is a pointer to one word per member, and a `bytes` member word points to a length-prefixed buffer (`bytesStructSchema?`, `lowerBytesStructPointer`). Constructor arguments are evaluated before the struct is allocated; a calldata value or slice, or a builtin encoding, is copied into a fresh zero-padded buffer, as solc copies calldata. The value binds a schema-checked memory struct descriptor, so `s.head`, `s.head.length`, `keccak256(s.head)`, `split(data).head` and struct arguments reuse the dynamic-struct paths. An unnamed helper result must return on every path. Named constructor arguments must be written in declaration order: solc's legacy pipeline evaluates them in declaration order and via-IR in written order, so a reverting slice written before a panicking scalar member would revert differently. An existing `bytes memory` buffer as a member (solc shares the pointer), root ABI returns of such structs, named struct results, member writes, reassigned struct locals, and members outside the ABI scalar/`bytes` schema fail closed with located diagnostics. |

`BytesNamedReturnSliceStructSequence` (fixture `bytes-named-return-slice-struct`) runs three equivalent variants A/B/C (baseline, renamed, and `unnamed-returns`, which rewrites the named returns as unnamed ones and the slice arguments and the struct as inline slices) over empty, short and word-boundary payloads and slice bounds on both sides of `start <= end <= length`. It also covers reassigned `bytes memory` parameters (bound from calldata, a slice, and a memory local) and locals, a named result read before its first assignment, struct members of scalar and `bool` type beside `bytes`, a positional constructor, a whole struct passed to a helper, and `abi.encode` of a struct. `BytesNamedReturnStatelessSequence` (fixture `bytes-named-return-stateless`) runs the issue's stateless shape (no state variables), a named `returns (bytes calldata out)` root, and a slice of a conditional calldata argument. The mutants `import-bytes-named-slice-default`, `-end`, `-start` and `-member-order` cover the empty named-return default, both slice bounds and the struct member layout; `-return-size`, `-param-size`, `-param-copy` and `-reassign-size` cover the size stored by `return <buffer>`, the callee-owned length and the word copy of a calldata argument bound to a `bytes memory` parameter, and the size rebinding of a reassigned local. `NamedStringReturnSequence` (fixture `named-string-return`) runs named `returns (string memory name)` roots (#2737) with one state variable, so the `stateVars.size > 1` gates stay off as in the issue's stateless snippet: the unassigned empty result, a literal, a storage string copied into the result, an early `return "literal"`, and a `string(abi.encodePacked(...))` result written back to storage, in variants A/B/C (baseline, renamed, and `unnamed-returns`, which returns each value explicitly).

### Development slice: root ABI parameters: `string` struct members, `S[]` and `bytes[]`

| Supported Solidity | Lowering boundary |
| --- | --- |
| `string` members of ABI-decoded `memory` / `calldata` struct parameters (#2711), beside scalars, `bytes` and arrays, and inside nested dynamic structs: scalar member reads, `bytes(s.label)`, `bytes(s.label).length`, `keccak256(bytes(s.label))`, `abi.encodePacked(bytes(s.label), ...)`, and storage writes `storedLabel = s.label` | `AbiSchema.root` maps a `string` member to `Member.bytesField name true`: `string` and `bytes` share the dynamic byte-array ABI encoding, so the member is decoded, bounds-checked (memory: eager `AbiLowering.memoryBytesField`; calldata: lazy `calldataBytesFieldHead`, a signed `slt` offset check like solc's `access_calldata_tail`, so a backwards member offset is accepted in calldata and rejected in memory) and read exactly like a `bytes` member. The flag only selects the model parameter's ABI type name (`ParamType.string`), pinned by kernel-checked `example`s in `StructStringMemberParamSequenceModel.lean`. A struct with a `string` member passed to a typed-interface staticcall is rejected (`typed interface staticcall struct arguments with string members are outside this slice`, `AbiSchema.membersHaveString`) until that re-encoding has differential coverage. |
| Root `S[] calldata` / `S[] memory` parameters of a flat scalar struct (#2708): `items.length`, `items[i].field`, loops, several arrays, arrays behind scalar / `bytes` / `T[N]` head words, `S calldata it = items[i]` / `S memory it = items[i]`, and `items[i]` as a struct helper argument | The parameter is member `w` (its ABI head word) of the root argument tuple, whose pointer is 4 and against which ABI offsets are relative: `MemParam.rootArrayWord = some w` with schema `AbiRootLowering.rootArraySchema w (AbiSchema.structArrayMember ...)` (`w` unread placeholder words, then the `structArray` member), and the identifier lowers to `.abiArray id w`. So the struct-member array readers apply unchanged. Entry decoding (`AbiRootLowering.rootArray`) follows solc's eager root decoding: calldata gets `abi_decode_t_array_*_calldata_ptr`'s head checks (`AbiLowering.scalarArrayCalldataHead` with `elementWords` = field count), memory the struct-array member copy (`memoryStaticArrayHead` + `materializeStaticStructArray`, `Panic(0x41)` before payload truncation). Like solc's `abi_decode_tuple`, the memory decoder allocates only the array and its elements, never a struct for the root tuple (`materializeFromCalldata (wrapper := false)`): the array pointer stays in a local (`AbiRootLowering.memberArrayMemoryPointer`, read by `MemParam.memoryMemberWord`), so every later allocation and its `Panic(0x41)` boundary is solc's. The element struct of `items[i]` is recorded on the parameter (`MemParam.rootArrayStructId`, resolved by `abiElementStructId`), so element locals and helper arguments bind like struct-member array elements. The head word computed in `bindRoot` is checked against the model parameters. |
| Root `bytes[] calldata` / `bytes[] memory` parameters (#2701): `data.length`, `data[i]`, `data[i].length`, `keccak256(data[i])`, `abi.encodePacked(data[i], ...)`, `data[i]` as a `bytes calldata` helper argument | The same root-tuple view with `Member.bytesArray`. `data[i]` checks `i < length` (`Panic(0x32)`) and binds a `bytes` descriptor (`CalldataBytesParam`) under a synthetic id, so the descriptor-based `bytes` lowerings (`.length`, hashing, packed encoding, `bytes calldata` helper arguments) apply to it; slices and `abi.decode` of `data[i]` stay rejected: in calldata after solc's `access_calldata_tail_t_bytes_calldata_ptr` checks (`AbiLowering.calldataBytesTailAt`, relative to the array data), in memory as the element pointer of the eager entry copy (`AbiRootLowering.materializeFromCalldata`'s `bytesArray` case: the pointer array, then `AbiLowering.memoryBytesAt` per element, as `abi_decode_t_array$_t_bytes_memory_ptr_$dyn_memory_ptr`). `string[]`, `bytes[]` struct members, element writes and `bytes[]` helper parameters fail closed. |

`StructStringMemberParamSequence` (fixture `struct-string-member-param`) runs A/B/C variants `baseline`, `renamed` (parameters and locals) and `members-renamed` (struct members and the state variables). It first runs a deterministic call list (`check_stateful.ROOT_PARAM_CALLS`) of well-formed inputs (empty, short and word-boundary labels, memory and calldata structs, a `string` beside a `bytes` member, `string` storage writes read back through a getter, a `string` in a nested dynamic struct) and malformed ABI inputs (member offsets past calldata, beyond 64 bits or backwards, `2**256 - 32`; lengths past the payload or beyond 64 bits; a dirty `uint16` / `bool`; truncated heads), then a `read()`. The mutants `import-root-param-string-member-pointer` and `-string-calldata-member` displace the byte buffer of a `string` member read from a memory struct (payload pointer) and from a calldata struct (member word). The rejection-suite controls `root-param-string-member-accepted` and `root-param-string-member-staticcall-rejected` pin both sides of the boundary.

`StructArrayParamSequence` (fixture `struct-array-param`) and `BytesArrayParamSequence` (`bytes-array-param`) run A/B/C variants `baseline`, `renamed` (parameters and locals) and `members-renamed` (struct members, helpers and the state variable). Each first runs a deterministic call list (`check_stateful.ROOT_PARAM_CALLS`) of well-formed inputs (empty and multi-element arrays, empty, short and word-boundary payloads, in- and out-of-range indices) and malformed ABI inputs (offsets past calldata or beyond 64 bits, a backwards `bytes[]` element offset `2**256 - 32` that calldata accepts and memory rejects, lengths past the payload or beyond 64 bits, dirty narrow fields, malformed element tails, truncated heads and elements), the `Panic(0x41)` boundary of every memory array allocation (the pointer array at length `2**59 - 6` / `2**59 - 5`, and a `bytes[]` element's allocation), and `items[i]` bound to calldata, memory and copied struct locals and passed to a helper, then a `read()`. The mutants `import-root-param-lowering-tuple` (root argument tuple pointer), `-lowering-bytes-copy` (base of the eager `bytes[]` element copy), `-bytes-element-bound` (the `data[i]` bound) and `-bytes-element-base` (the calldata tail base) and `-lowering-memory-wrapper` (allocates a struct for the root tuple of a memory array, moving the `Panic(0x41)` boundary), and the rejection-suite controls `root-param-struct-array-accepted`, `-struct-array-element-local-accepted`, `-struct-array-element-helper-accepted`, `-bytes-array-accepted`, `-string-array-rejected` and `-struct-array-dynamic-member-rejected` cover the arrays.

### Development slice: `string` and `bytes` storage variables (`encoding == "bytes"`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `string` and `bytes` storage state variables (`layout.encoding == "bytes"`, `numberOfBytes == 32`) | Registered in `ImportedContract` with `FieldType.uint256` at their `solc` storage slot (`storageBytesVars`), while `Expr.storageArrayElement field slotExpr` and `Stmt.setStorageArrayElement field slotExpr value` on scalar `FieldType.uint256` fields denote and compile computed-slot `sload`/`tload` and `sstore`/`tstore` directly at `evalExpr slotExpr` (`Denote.evalExpr`, `Denote.execStmt`, `ExpressionCompile.compileStorageArrayElement`, `StorageWrites.compileSetStorageArrayElement`, `SourceSemantics.evalExpr`, `SourceSemantics.execStmt`, `Coverage`, `Quote`, `TransactionAccess`). |
| Storage `string` / `bytes` length reads (`b.length`, `bytes(s).length`, `bytes(string(b)).length`), memory materialization (`lowerStorageBytesRead`), whole-value writes (`s = ...`, `b = ...`), and `delete s` / `delete b` | `lowerStorageBytesLength` decodes the packed Solidity storage header word `raw = sload(slot)` (reverting with `Panic(0x22)` / `0x4e487b710000000000000000000000000000000000000000000000000000000000000022` when `(raw & 1) == ((raw & 255) / 2)` for `0 < (raw & 255) < 64`), returning `(raw & 255) / 2` for short values (`(raw & 1) == 0`) and `raw / 2` for long values (`(raw & 1) != 0`). `lowerStorageBytesRead` allocates a 32-byte-aligned memory buffer via `AbiEncoding.reserve` and either stores `raw & ~255` (short `< 32` bytes) or copies `(len + 31) / 32` words starting at `keccak256(slot)` via `Stmt.forEach` (`keccak256(abi.encode(uint256(slot))) + i`), enabling storage `string` / `bytes` values in `return`, local `string memory` / `bytes memory` initializers, helper arguments, `keccak256(...)`, `abi.encodePacked(...)`, and `bytes.concat` / `string.concat`. `lowerStorageBytesWrite` and `lowerStorageBytesDelete` validate the old storage header (`Panic(0x22)`), zero out any previously occupied long-storage words (`oldWords > newWords` or `newLen < 32`), and write either the packed short header `(firstWord & ~mask) \| (len * 2)` or the long header `len * 2 + 1` plus cleaned payload words at `keccak256(slot) + i`. Storage `bytes` indexing (`b[i]`), `.push` / `.pop`, storage-pointer locals, non-statement assignments, and reads shadowed by unsupported locals/parameters fail closed with located diagnostics. |

### Transient state variables (solc 0.8.28 and later, Cancun and later)

`transient` state variables come from solc's `transientStorageLayout` output instead of
`storageLayout`. They admit the same scalar types as persistent scalar state variables
(`bool`, `address`, contracts, `uintN`, `int256`, `bytes32`) and lower to the same reads,
writes, compound updates, `delete`, assignment expressions, tuple assignments and public
getters, on `Field.isTransient` fields (`tload` / `tstore`). Packed neighbors keep their
bytes; persistent storage at the same slot number is a separate channel. A modifier lock
follows the transaction boundary: a fresh transaction clears it, a callback in the same
transaction sees it. Narrow signed integers, `bytes1`..`bytes31`, enums and function
pointers fail closed with a located `unsupported transient scalar storage type`.
A root whose closure accesses a transient variable and contains inline assembly fails
closed at one of its assembly blocks, including Yul `tload` / `tstore` and `x.slot`. This
is a conservative bound for this slice: interactions between assembly and transient
variables are not yet covered by controls. A transient variable that shares its name
with a persistent one in the inheritance chain is not given a layout: roots that use it
fail with the shadowed-declaration diagnostic, and roots that reach only the persistent
variable import unchanged.

### Development slice: multi-statement `InlineAssembly`, Yul locals & full-word local/parameter assignments, `tstore`, `addmod` / `mulmod`, and `*=`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Multi-statement `InlineAssembly` blocks in root, single-return helper, void/multi-return helper, and loop bodies (`lowerAssemblyStmts`) | Supports sequential `YulVariableDeclaration` (`let x := expr` or default-zero `let x`), single-target `YulAssignment` (`x := expr`) to block-scoped Yul locals, the active single-return helper result (`checkYulReturnTarget` + `cleanHelperResultExpr`), or unshadowed full-word (`uint256`, `int256`, `bytes32`) writable Solidity scalar locals and helper/modifier parameters (`inlineAssemblyAssignedIds`), and `YulExpressionStatement` `tstore(slot, val)` (`Stmt.tstore`, covered by `Coverage.executableStmtCovered`, `Coverage.abiHeaderPreservingStmt`, `Quote.quoteStmt`, and `TransactionAccess.statementAccesses` with reflexive `rfl` arm-pin lemma `execStmt_tstore_arm`). Yul assignments to narrow Solidity locals/parameters (`uint8`–`uint248`, `address`, `bool`, `enum`), storage `.slot` / `.offset` references, multi-variable Yul declarations/assignments, and unsupported Yul statements (`for`, `switch`, `leave`, `mstore`, `sstore`) fail closed with located diagnostics. Yul `if c { ... }` lowers to a conditional that runs the body exactly when `c` is a nonzero word, in every contract (formerly only with more than one state variable; `YulIfStateCountChecks`). Yul `revert(offset, 0)` lowers to a revert with no data (`revertEmpty`) in every contract. A nonzero size lowers to `Stmt.revertMemory` (revert data = those memory bytes) only for a literal range below 0x40 (the scratch words) whose every byte the same Yul block wrote on every path (`yulWrittenBytes`; a write inside a Yul `if` body does not count after it; a restored free-memory pointer at 0x40 never counts, since it holds solc's pointer, not the model's), which covers the custom-error shapes `mstore(0, sel) revert(0x1c, 4)`, `mstore(0, sel) mstore(0x20, arg) revert(0x1c, 0x24)`, `mstore(0, shl(224, sel)) mstore(4, arg) revert(0, 0x24)` and `revert(0, 4)` over a left-aligned selector. Inlined helper calls follow the same rule: neither the helper name nor the selected error’s declared arguments determine the payload. Any other range, or a run-time offset or size, is rejected with a location (`YulRevertDataChecks`, `YulRevertMemorySequence`, `YulEmptyRevertSequence`). Yul `mcopy(dst, src, size)` (EIP-5656) with a literal zero size lowers to its operands' effects only (no copy, no memory expansion, whatever the offsets); a nonzero copy lowers only for literal source and destination ranges inside the scratch words below 0x40 whose every source byte the same Yul block wrote on every path, to snapshot loads of both scratch words and masked, shifted stores of the destination words (memmove semantics on overlap in either direction); the copied bytes then count as written. For a nonzero copy, run-time offsets or sizes, ranges reaching 0x40, unwritten source bytes and copies between heap buffers (#2620) are rejected with a location (`YulMcopyChecks`, `YulMcopySequence`). |
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
| Storage struct enum members and `mapping(K => Enum)` members | For layout-decoded structs, assignment of an enum literal and member/element `delete` use an 8-bit masked write (`mapping(K => Enum)` requires a non-enum key `K`; Yul assignments to enum variables, non-literal enum assignments, and whole-struct deletion with packed enums are not admitted). Reading sibling fields does not validate the enum. A direct, single enum return with no modifier epilogue checks the extracted byte against the enum declaration (`Panic(0x21)`); initializing an unreferenced enum local does not. Other consumers of a storage enum (including comparisons and passing it to a helper), raw-slot enum access, and generated public struct getters returning an enum are outside this slice. `StorageStructEnumChecks` pins dirty reads, physical words after writes/deletes, and rejected forms. |
| Extended mapping key types (`mappingKey`) and mapping struct member types (`buildField`, `memberRead`, `lowerEffect`) | `mappingKey` accepts `address`, `address payable`, `contract` / `interface` types, `bytes32`, `int256`, `bool`, `enum` types, and `uint8`–`uint256` as one- and two-key mapping keys; narrow signed (`int8`–`int248`), fixed-bytes (`bytes1`–`bytes31`), and reference keys fail closed. `buildField` accepts `uint8`–`uint256`, `int8`–`int256`, `address`, `address payable`, `contract` / `interface` types, `bytes32`, and `bool` as packed or full-word mapping-struct members, recording `booleanMembers` on `FieldInfo` so `memberRead` and `lowerEffect` normalize boolean struct member reads and writes with `Expr.logicalNot (.logicalNot ...)`. Narrow signed members (`int8`–`int248`) are recorded with their width in `signedMembers`, and `memberRead` sign-extends their reads, as solc does on load; members of structs held in storage arrays are sign-extended in `readRawStructScalar`. `SignedStructMemberReadSequence` (fixture `signed-struct-member-read`, variants `baseline` / `renamed` / `local-reads`) stores negative `int24` / `int16` / `int128` members, including values that use each member's top byte, in a storage array, a mapping and a state variable and reads them through casts, signed comparisons, checked arithmetic, a storage reference, a memory copy and inline assembly reading the raw stack word of a local; mutants `import-signed-struct-member-raw-read` and `import-signed-struct-member-layout-read` drop either extension, and `import-signed-struct-member-raw-read-width` and `import-signed-struct-member-layout-read-width` extend either read from one byte too low. |
| `string` / `bytes` members of storage structs (`decodeStructLayoutMembers`) | A struct member whose layout type is `t_string_storage` or `t_bytes_storage` (`encoding == "bytes"`, 32 bytes, byte offset 0) is recorded as an opaque member (`report.opaqueMembers`) instead of rejecting the whole struct layout, so scalar siblings before and after it keep solc's slot and offset and import in mapping-backed (one and two keys), storage-reference and plain state-variable structs. The dynamic member itself stays outside the slice: reading, writing, `delete`, `.length` / `.push` through it fail closed (`member ... is opaque in this slice`), and so do whole-struct `delete`, whole-struct assignment, storage-to-memory copies and public struct getters. `StorageStringMemberSequence` (fixture `storage-string-members`, variants `baseline` / `renamed` / `direct-members`) writes and reads packed siblings of untouched `string` and `bytes` members; `check_storage_rejections.py` cases `member-string-*` / `member-bytes-*` cover the accepted sibling shapes and the located rejections. String member contents are not modelled. |
| Terminal root `InlineAssembly` assigning to a single named scalar return variable | When a root function has a single named scalar return parameter (`rootNamedReturn`), empty modifier post-statements (`rootPost.isEmpty`), and a terminal `InlineAssembly` statement that only assigns to the return declaration without reading it in Yul (`yulOnlyAssignsDecl`), `lowerRootStatements` routes the assembly block through `helperResult := some (rbinding, rty)` and `cleanHelperResultExpr` before `lowerRoot` emits `Stmt.returnValues`, matching `solc` ABI return masking on narrow return types (such as `address`) while rejecting Yul reads of narrow root return variables. |

### Development slice: user-defined value types (`type T is U`), direct parameter assignments, chained/conditional multi-returns, zero-arg custom-error helpers, Yul memory-array `keccak256`, and struct-array element helper calls

| Supported Solidity | Lowering boundary |
| --- | --- |
| User-defined value types (`type T is U`, `T.wrap(x)`, `T.unwrap(v)`, `using L for T`) | `index` records `UserDefinedValueTypeDefinition` nodes in `userValueTypeById` and `userValueTypes`, mapping both qualified (`Contract.T`) and unqualified (`T`) names to their underlying elementary type string `U`. When `U` is a supported non-enum scalar (`uint8`–`uint256`, `int256`, `address`, `bool`, `bytes32`), `mType` normalizes UDVT type descriptions to `U`, `selectFunction` matches either the UDVT name or `U`, and `lowerCall` lowers `T.wrap(arg)` and `T.unwrap(arg)` via `convert U (← mType arg) (← lowerExpr arg) arg`. As `abi.encode` / `abi.encodePacked` / `abi.encodeWithSelector` arguments, `checkEncodingScalar` admits `T.wrap(x)` / `T.unwrap(x)` as the identity on the underlying word and checks only `x`, so a reverting helper beneath the conversion is still rejected at that call, and a state-changing one only outside an ordered `abi.encode` (below) (`AbiEncodeUdvtSequence`, `AbiEncodeUdvtChecks`). UDVTs with unsupported underlying types (such as `bytes16` or `int128`) fail closed. |
| State-changing internal helpers as `abi.encode` arguments (`keccak256(abi.encode(TYPEHASH, owner, spender, value, _useNonce(owner), deadline))`) | Both solc 0.8.34 pipelines evaluate `abi.encode` arguments left to right before encoding. When the `abi.encode` builtin has an all-static argument list and some argument contains a state-changing call (`statefulCallIn`), `lowerAbiEncodeArgs` runs with `orderedEffects`: `checkEncodingScalar` admits internal helpers with a body (state-changing or reverting, also beneath a conversion or `T.unwrap`), and every non-literal word is bound to a temporary at its own position, so each effect runs once and a storage read between two helpers sees only the earlier write (`AbiEncodeStatefulSequence`, A/B/C check `abi-encode-stateful`). Located rejections (`AbiEncodeStatefulChecks`): the same arguments in `abi.encodePacked`, `abi.encodeWithSelector`, `abi.encodeWithSignature` and `abi.encodeCall`; a dynamic (`bytes`, `string`, array) argument or a struct argument beside the helper (solc reads a struct only while encoding, after the helper has run); external calls and function pointers; and such an ordered `abi.encode`, hashed or not, inside another encoding form with more than one argument (`abi.encodePacked`, `bytes.concat`, `string.concat`, whose arguments are walked last to first; `statefulAbiEncodeIn`). |
| `x++`, `--m[k]` and `x = v` as call and `abi.encode` arguments (`_hash(to, value, nonce++)`, EIP-2612 `keccak256(abi.encode(TYPEHASH, owner, spender, value, nonces[owner]++, deadline))`) | Both solc 0.8.34 pipelines evaluate these arguments left to right, each write at its own position (checked on Anvil for pre/post `++`/`--` of a state variable and of a mapping element, `=` and `+=`, in internal calls, `abi.encode` and `keccak256(abi.encode(...))`; no pipeline difference). In a direct internal call whose arguments are `++`/`--` of a storage or local identifier or of an indexed element with literal/identifier keys, `x = v` with an effect-free scalar `v`, effect-free scalar siblings or calldata identifiers, every scalar argument is bound to a temporary at its position (`lowerCallArgs` `sequence`). In an all-static `abi.encode`, such an argument makes the encoding ordered (`lowerAbiEncodeArgs`), which also admits indexed sibling reads; a hashed ordered encoding may be an argument of `abi.encodePacked`, which writes each argument at its position (`AssignmentArgumentSequence`, A/B/C check `assignment-arguments`). Located rejections (`AssignmentArgumentChecks`): the same arguments beside a dynamic or struct `abi.encode` argument, inside `abi.encodePacked` directly or in an encoding nested in `bytes.concat` / `string.concat` / a non-ordered encoding (`assignmentAbiEncodeIn`), `m[k] = v` and compound assignment expressions, and call updates with computed keys. |
| Pure or view helpers returning `string` / `bytes` as `abi.encode` arguments and root return tuple components (`abi.encode(TYPEHASH, _name(), ...)`, the ERC-5267 `eip712Domain()` tuple) | The helper body is inlined by `inlineStringFn` (a packed one-word string decoded with assembly, a storage `string` fallback, a custom-error revert on a bad length byte). In `lowerAbiEncodeArgs`'s dynamic path such an argument may revert: both solc 0.8.34 pipelines evaluate the arguments left to right, the helper's statements run at its own argument position, and every revert of a scalar or memory sibling (checked arithmetic, other helpers) sits in its `pre` at its position, so of two failing arguments the first one's revert data is returned (`AbiEncodeStringHelperSequence`, A/B/C check `abi-encode-string-helper`: empty, 3-, 31-byte packed, 32-, 33-byte and empty fallback strings, a `bytes` helper, static siblings, hashed and unhashed, nested, root tuple). A string literal against a declared `bytesN` parameter or return component (the `hex"0f"` `bytes1 fields` of `eip712Domain()`) is that static left-aligned head word (`lowerExprAs`), not a dynamic `string`. Located rejections: such a literal in an all-static argument list (`unsupported non-numeric literal`, e.g. a typed interface call `I(a).f(hex"0f")` with a `bytes1` parameter) and as event data for a `bytesN` parameter (the data is encoded by the arguments' own types). Located rejections (`AbiEncodeStringHelperChecks`): a state-changing `string` helper beside another argument, a state-changing scalar helper beside one (as above), a calldata or storage argument beside a reverting one (solc reads a storage `string` / `bytes` and may validate a calldata array only while encoding, after the helper), a reverting scalar helper (`checkEncodingScalar`), and a reverting multi-argument `string.concat` / `bytes.concat` in the argument or its helpers (`revertingConcatIn`: `lowerPacked` lowers concat arguments last to first, solc left to right). |
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
| Internal/private/library `StructName memory` helper parameters for flat scalar-member structs (`FlatStructLocal` / `CallArg.flatStruct`) | When a `StructName memory` helper parameter is not covered by the existing `AbiRootLowering` calldata/memory root-ABI schema, `lowerCallArgs` accepts a `FlatStructLocal` identifier, a positional `StructName(...)` constructor, or a storage-to-memory copy of a scalar-member storage struct (`lowerFlatStructValue`), evaluating and converting all scalar members at the call site into `CallArg.flatStruct`. `bindHelperParams` binds fresh per-member local variables in `flatStructs` and rejects helpers that reassign the struct parameter (`reassigned struct parameters are outside this slice`). When the argument is the caller's own memory struct local, solc passes a reference, so a member write in the helper (assignment, compound assignment, `++`/`--`, `delete`, a tuple-assignment target, also through a nested helper or a `using L for S` receiver call) and returning the parameter (directly, in parentheses, from a conditional or as a tuple component) would change or alias the caller's struct; the copy cannot model that, so both reject with a location (`MemoryStructParamChecks`). The rule is conservative: a write or a return is rejected even when the caller never reads or writes either struct afterwards. Reads, writes to a struct built in the argument or copied from storage, and writes to the helper's own struct import. Storage-to-memory copies of structs with mapping/array/opaque members fail closed (`storage struct with non-scalar members cannot be copied to memory in this slice`). |
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
| `mapping(K => V) storage` helper parameters bound to a mapping member of a storage struct (`credit(book.bal, who, v)`, `credit(books[id].bal, ...)`, `credit(b.bal, ...)` through a `S storage` local or an ERC-7201 raw-slot struct) | `lowerCallArgs` computes the member mapping's slot once at the call (the struct's base slot, after its outer keys, plus the member's word offset) and `bindHelperParams` binds the parameter to that raw slot, exposing `<param>.slot` in assembly. Indexing, compound writes, `delete m[k]`, struct-valued `m[k].a` (packed members keep their siblings), signed keys (`int8`, cleaned from their source type like any mapping key) and forwarding to another helper lower like the member itself; two parameters may denote the same mapping. Packed value types (`mapping(K => uint8)`, `mapping(K => bool)`), nested `mapping(K1 => mapping(K2 => V))` members of ordinary storage structs (opaque), top-level mapping state variables of scalars as arguments (struct-valued ones: next row) and arguments that assign (`i++`) keep their located rejection (`storage-mapping-argument-*-rejected`). The lowering does not depend on the state-variable count (formerly only with more than one state variable; `StorageMappingArgumentStateCountChecks`, #2830). |
| A one-key mapping state variable of structs passed to a `mapping(K => S) storage` helper parameter, typically an internal library function bound with `using ... for` that returns a storage pointer to an entry (`S storage s = entries.get(k)`, where `get` reads `entries[k]`, checks a `require` with a custom error and returns it) | The parameter is bound to the state variable itself (`lowerCallArgs`, `bindHelperParams`, `lowerRef`), so `m[k]` in the helper is the same storage path as `entries[k]` in the caller, and the returned pointer is that entry. As solc (legacy and via-IR): the helper's `require(..., E())` / `require(..., E(k))` reverts with the exact custom-error payload at its position; writes and reads through the pointer, packed and nested struct members included, hit the slots of `entries[k].field`; two pointers to one entry alias each other and a later direct write is seen through an earlier pointer; the parameter can be forwarded to another helper, and the key can be any side-effect-free expression. Located rejections (`storage-pointer-mapping-helper-*-rejected`): a helper that returns different entries under a condition, a pointer built in assembly from `<param>.slot` (the parameter has no Yul name, nor does a caller's same-named local leak in), a reassigned pointer local, two-key or scalar-valued mapping state variables as arguments, a key with a side effect (`get(bump(k))`, `get(i++)`: the existing evaluation-order gates), a discarded result (`entries.get(k);`), a named result assigned before further statements, and a member write on the call result (`entries.get(k).a = v`). `StoragePointerMappingHelperSequence` (A/B/C, `storage-pointer-mapping-helper`); mutants `import-storage-pointer-mapping-helper-*`. |
| `<param>.slot` of top-level and mapping-indexed storage struct helper parameters in `InlineAssembly` (`tload(not(self.slot))` over a struct wrapper, `sload(add(self.slot, k))`, `sstore(self.slot, v)`) | When a helper's assembly names `<param>.slot` (`yulReferencesDeclSlot`) for a non-reassigned `S storage` parameter bound to `SPath.zero`, `SPath.one` or `SPath.two`, `bindHelperParams` binds it to the slot from the resolved storage layout (`storageStructPathSlot`): the layout slot of a top-level struct, or `keccak256(abi.encode(k, slot))` / its two-key nesting (`computeSPathBaseSlot`), computed at the call. `<param>.slot` of a nested storage struct member, reassignment of `<param>.slot` in assembly, and `<param>.offset` fail closed with located diagnostics, and a `<name>.slot` binding never stands in for another declaration of the same name: inlined callees do not inherit it, a same-named local (inner block or modifier) drops it, and a modifier's state variable `X.slot` seen beside a parameter `X` is rejected (`shadowed storage declaration`). `StorageStructParamSlotSequence` (fixture `struct-param-slot`, variants `baseline` / `renamed` / `direct-library-calls`) compares the slot words and the aliased `sload` / `sstore` / transient reads with solc; mutants `import-storage-struct-param-slot-top` and `-keyed`. |
| Root return tuples with dynamic components: `returns (T[] memory)`, `returns (address[] memory xs, uint256[] memory ys)`, `returns (uint256[] memory items, uint256 next)`, `returns (string memory, bool[] memory, bytes memory)`, named or unnamed (#2707, #2723) | `functionDynamicTupleReturn?` selects a root whose return parameters include a scalar `T[] memory` array, or `bytes` / `string memory` beside other components, and are otherwise ABI scalars (a lone `bytes` / `string` result keeps the rows above; an empty body keeps `functionEmptyBodyArrayReturnType?`). It does not depend on the number of state variables. Named results are bound before the body (`bindRootDynamicTupleResult`): a `T[]` result is solc's zero-length array at `0x60` and reassignable like a `T[] memory x;` local, a `bytes` / `string` result an empty rebindable buffer, a scalar result `0`. Each `return e` / `return (e₀, …)`, and fallthrough of an all-named root, is encoded by `lowerDynamicTupleReturn` with the `abi.encode` encoder (`lowerAbiEncodeArgs` against the declared return parameters, so scalars are converted to the declared types) into a fresh memory buffer, runs `env.rootPost`, and returns it through the closed `SolidityReturnMemory` transport, as dynamic struct returns do. A `T[]` component may be an array binding (local, parameter or named result, encoded exactly as `abi.encode` encodes it), `new T[](n)`, an array helper result (`lowerDynArrayValue`), or a dynamic storage array of supported scalars (a state variable, storage pointer or struct member), copied into memory first with `copyStorageDynamicArrayToMemory` as solc does. Unnamed results reaching the end of the body, effectful non-identifier array components beside other components, a memory-writing helper beside a memory read in the same tuple, struct and fixed-size array components, and `T[] calldata` results fail closed with located diagnostics (`T[] calldata` results at the return parameter, `calldata array root return values are outside this slice`, whatever the state-variable count; `RootArrayReturnStateCountChecks`, #2830). |

For `returns (T, bytes memory)`, with named or unnamed root results, a root may also `return helper(args)` (#2803). A direct internal/private helper with matching types and named results can assign them and fall through. The bytes result may remain empty or be assigned from `abi.encode` or `abi.encodePacked`. The call runs once, then the root encodes the helper's scalar and byte buffer, keyed by the helper's result declarations: values the root assigned to its own named results earlier are not returned, even when the names coincide. `SequenceFixture.run` is #2803's `(bool ok, bytes memory data)` shape and `runShadow` assigns the root results before forwarding; both cover the empty tail, a 32-byte tail, a `require` revert and a checked-overflow panic after a storage write. A local alias of the helper's bytes result keeps the old buffer when the result is rebound (`forwardBytes`); element writes through the result or an alias fail closed. `runBranch` forwards from a non-tail `if` branch and otherwise falls through with its own named results. Modifiers on the root or its helpers (including nested helpers), explicit tuple-helper returns, and inline assembly anywhere in the forwarded call tree are outside this forwarding path. Anywhere in a root containing such a forward, including the root body, typed external call results, external `bytes` results, `try`/`catch`, contract creation, `abi.encodeCall` with a `bytes` parameter, effectful or memory-writing `abi.encodePacked` arguments and stateful binary operands also fail closed with located diagnostics.

`DynamicArrayRootReturnSequence` (fixture `dynamic-array-root-returns`, two state variables) runs a named `(address[] memory, uint256[] memory)` pair assigned `new` arrays in a loop and early-returned as `(members, amounts)` with a storage array component, `return members;` from `returns (address[] memory)` (#2723), an explicit `(uint256, address[] memory, uint256)` tuple with a storage array in the middle, and a named single `address[]` result filled from storage on fallthrough. `DynamicArrayRootReturnStatelessSequence` (fixture `dynamic-array-root-returns-stateless`, no state variables) runs a named `(uint256[] memory items, uint256 next)` result (a paginated-list shape) with an unassigned early return, a helper result, a `new uint256[](n)` component and a `uint8` value widened to the declared `uint256`, a lone unnamed `uint256[]` helper result (#2697's shape), a `uint8[] memory` root parameter returned as is (re-encoded; an out-of-range element reverts in decoding), and a named `(string, bool[], bytes)` tuple. Both run variants A/B/C (baseline, renamed, and `unnamed-returns`, which returns every value explicitly). The mutants `import-dynamic-root-return-zero-array` and `-size` cover the zero-length initial value of a named array result and the size of the returned tuple buffer.

### Development slice: dynamic storage arrays of scalar-member structs (`S[]`), struct-valued mappings inside storage structs, `Checkpoints._unsafeAccess`, binary-search `while (low < high)` loops, named struct constructors, and flat-struct helper returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Dynamic storage arrays of scalar-member structs (`S[]`, `Checkpoints.Checkpoint208[]`, `TrancheRecord[]`) at top level, inside storage structs, and inside ERC-7201 raw-slot structs (`FieldInfo.dynamicArrayStructId`, `StructDynamicArrayInfo.elemStructId`) | `buildField`, `decodeStructLayoutMembers`, and `resolveRawStructInfo` accept 1-D dynamic storage arrays `S[]` when `S` is a struct whose members are all supported scalars (`elemInfo.mappings.isEmpty && elemInfo.dynamicArrays.isEmpty && elemInfo.subStructs.isEmpty && !elemInfo.scalars.isEmpty && elemInfo.wordCount > 0`) and `base.numberOfBytes == elemInfo.wordCount * 32`. `storageDynamicStructElementPath` checks `index < len` (`Panic(0x32)`) and resolves `arr[index]` to `SPath.rawSlot elemSid (keccak256(abi.encode(arrSlot)) + index * wordCount)`, enabling member reads/writes, whole-struct reads (`S memory s = arr[i];`), whole-struct writes (`arr[i] = s`), and `delete arr[i]` (zeroing all `wordCount` slots). `pushStorageDynamicStructArray` lowers `arr.push(s)` and `arr.push()` (returning `SPath.rawSlot elemSid (keccak256(abi.encode(arrSlot)) + oldLen * wordCount)` for `S storage p = arr.push();` and chained `arr.push().member = v`), `popStorageDynamicArray` zeroes all `wordCount` slots of `newLen` on `arr.pop()` (`Panic(0x31)` on empty array), and `deleteStorageDynamicArray` zeroes `oldLen * wordCount` words on `delete arr`. `S[] storage` parameters and locals bind `(fieldName, slotExpr, elemTy, some elemSid)` in `storageDynamicArrayVars` and expose `<name>.slot` in `Env.yulNames`. Struct elements with nested arrays, mappings, or sub-structs fail closed (`unsupported storage encoding dynamic_array`). |
| Struct-valued mappings inside storage structs and ERC-7201 raw-slot structs (`mapping(address => Checkpoints.Trace208) delegateCheckpoints`, `StructMappingInfo.valueStructId`) | `resolveRawStructInfo` and `decodeStructLayoutMembers` accept `mapping(K => V)` struct members when `K` is a supported `mappingKey` and `V` resolves to a supported `RawStructInfo` (`valueStructId := some valSid`). Indexing `s.map[k]` in `lowerRef` hashes `leafSlot := keccak256(abi.encode(k, mapBaseSlot))` and returns `Ref.path (...) (.rawSlot valSid (.localVar leafSlot))`, enabling nested struct member, dynamic-array, and helper-receiver accesses such as `$.delegateCheckpoints[voter].push(...)` and `$.delegateCheckpoints[voter].upperLookup(...)`. |
| Prefix Yul statements before `result.slot := ...` in storage-pointer helpers (`Checkpoints._unsafeAccess`) | `inlineStorageRefFn` supports internal/private/library helpers returning `StructName storage result` whose `InlineAssembly` block executes prefix Yul statements (such as `mstore(0, self.slot)`) before a final `result.slot := add(keccak256(0, 0x20), pos)` assignment, lowering the prefix statements via `lowerYulStmtSlice` and returning `SPath.rawSlot retStructId (.localVar slotTmp)`. Statements after `result.slot := ...` or missing slot assignments fail closed (`storage pointer helper assembly must end with a single slot assignment`). |
| Binary-search `while (low < high)` / `while (high > low)` loops (`Checkpoints._upperBinaryLookup`, `Checkpoints._lowerBinaryLookup`) | `lowerWhile` recognizes `while (low < high)` and `while (high > low)` over distinct writable unsigned integer locals/parameters `low` and `high` of matching bit width (`isBinarySearchMidpointExpr`, `isBinarySearchStepStmt`): the loop body must be `[VariableDeclarationStatement mid = midpoint(low, high), IfStatement ...]` where `midpoint(low, high)` is `(low + high) / 2`, `(low + high) >> 1`, `(low & high) + (low ^ high) / 2`, `low + (high - low) / 2`, or a 2-argument pure helper returning that midpoint (`Math.average(low, high)`), and the `if / else` branches assign `high = mid` in one branch and `low = mid + 1` (or `1 + mid`) in the other while leaving `low`, `high`, and `mid` otherwise unmodified. Lowers to `let bound := sub high low; forEach iter bound [ite (lt low high) body []]`, which executes at most `high - low` iterations (and strictly halves `high - low` on every active step). Non-narrowing branches or modified midpoint variables fail closed. |
| Named struct constructor arguments (`StructName({fieldB: b, fieldA: a})`) and helpers returning flat `StructName memory` (`inlineFlatStructFn`) | `lowerFlatStructValue` supports named `structConstructorCall` arguments (`names.size == args.size`) when every argument is pure/stateless (`!statefulCallIn arg && !assignmentIn arg`), evaluating each argument once into a temporary in call-site order and assembling member values in struct declaration order (rejecting stateful or assignment arguments so evaluation order can never diverge). `inlineFlatStructFn` and `lowerVoidHelperFrom` (`flatStructHelperResult`) inline internal/private/library helpers returning a single flat scalar-member `StructName memory` (`Checkpoints.at`, `_makeRecord`), supporting named and unnamed return parameters, `if / else` early returns, conditional struct expressions (`cond ? s1 : s2`), member projections (`s.at(0)._value`), local initializations (`Checkpoint208 memory c = _unsafeAccess(...);`), and discarded flat-struct/multi-return helper calls in `lowerEffect`. |

### Development slice: bounded sign-flip self-calls (`wadExp(-x)`, `WadExpAndThreeKeyMappingSequence`), `while (low != high)` binary search with `unchecked` blocks, 3-key scalar and struct mappings, and top-level fixed-size unsigned scalar storage arrays (`uintN[L]`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| Bounded 1-step `int256` sign-flip self-calls (`WadExpLib.wadExp(int256 x)`: `if (x < 0) return 1e36 / wadExp(-x);`, `inlineSignFlipSelfCallFn?`, `inlineSelfSignFlipTarget`) | `inlineSignFlipSelfCallFn?` recognizes single-return internal/private/library helpers with one `int256` parameter `x` (neither directly nor compound-assigned in the body) whose leading statement is `if (x < 0)` (or `if (0 > x)`) with an empty `else` branch, where the `true` branch unconditionally returns an expression containing a single self-call `fn(-x)` (`containsSelfNegCall` / `countCallsToId` == 1) and the remaining statements after the `if` contain zero self-calls (`countCallsToId` == 0). Lowers by evaluating the non-negative (`false`) continuation once for `x >= 0` and once for `-x` inside the `x < 0` branch (binding `inlineSelfSignFlipTarget := some (fnId, paramId, negResultVar)` so `fn(-x)` resolves to `negResultVar` without recursion). General recursive calls or self-calls in the non-negative continuation still fail closed (`recursive helper call <name>`). |
| Binary-search `while (low != high)` / `while (high != low)` loops with `low == 0` at loop entry and `unchecked { ... }` loop bodies (`WadExpLib.ratioToLevel`, `Env.zeroInitLocals`, `unwrapUncheckedBlockStmts`) | `Env.zeroInitLocals` tracks local variables initialized to literal `0` (`uintN low = 0;` or uninitialized default `uintN low;`) and clears membership whenever a statement can assign or mutate the local (`stmtModifiedIds`). `lowerWhile` admits `while (low != high)` and `while (high != low)` alongside `<` / `>` when `lowId ∈ env.zeroInitLocals` (failing closed with `binary-search while (low != high) requires low to be zero at loop entry` when `low` is non-zero or modified before the loop), because `0 = low <= high` and `mid = midpoint(low, high) < high` whenever `low < high`, so both `high = mid` and `low = mid + 1` preserve `low <= high` and terminate in at most `bits` iterations. Both the outer `while` body and the inner `if / else` branches unwrap `UncheckedBlock` wrappers (`unwrapUncheckedBlockStmts`) while preserving unchecked arithmetic semantics during statement lowering. |
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
| Yul assignments of provably-bounded expressions to narrow non-enum scalar locals (`uint8 v; assembly { v := byte(0, mload(add(signature, 0x60))) }`, `isProvablyBoundedYulExpr`) | `lowerYulDirectAssignmentTarget` admits Yul assignments to narrow non-enum scalar locals/parameters (`bool`, `uint8`–`uint248`, `address`) when the lowered RHS expression is provably bounded by `2^bits` (`isProvablyBoundedYulExpr`: `.literal n` with `n < 2^bits`, `.byte _ _` for `bits >= 8`, `.lt`/`.gt`/`.slt`/`.sgt`/`.eq`/`.logicalNot` for `bits >= 1`, `.bitAnd` with a mask `< 2^bits`, `.shr` by `>= 256 - bits`, or `.mod` by `0 < m <= 2^bits`). Integer locals also accept unbounded Yul words independently of the number of state variables. Same-width stack copies retain the word; numeric comparisons, checked arithmetic, shift counts and widening conversions consume the declared operand width. Legacy wrapping addition/subtraction/multiplication and left shifts can leave high bits visible in Yul where via-IR cleans the result. Unbounded writes to ordinary address or bool locals still fail closed. |
| Scalar `typeConversion` casts in custom-error revert arguments (`revert ECDSAInvalidSignatureLength(uint256(errorArg))`) | `lowerErrorArguments` accepts single-argument `typeConversion` calls whose inner expression is an identifier bound in `Env.values` (such as `uint256(errorArg)` where `errorArg` is `bytes32`), lowering and converting the argument via `convert errorParamType (← mType argument) (← lowerExpr argument) argument`. |
| Raw `bytes32` slot wrappers `StorageSlot.getStringSlot(bytes32 slot)` and `StorageSlot.getBytesSlot(bytes32 slot)` (`inlineStorageStructFn`) | When an internal/private/library storage-pointer helper returns a 1-member wrapper struct whose only member has type `string` or `bytes` (any member name, e.g. `struct { string value; }`) via a 1-statement `r.slot := slot` assembly block (`prefixYstmts.isEmpty && sMembers.size == 1` and the member type is `string`/`bytes`), `inlineStorageStructFn` binds `slot` to a fresh local and returns `SPath.bytesSlot ("", .localVar slotBinding) isString`, enabling member reads, `.length`, writes, `delete`, and `string storage` / `bytes storage` helper arguments on raw `bytes32` slots. |

### Development slice: `Create2.computeAddress`, `Clones.predictDeterministicAddress`, `keccak256(_msgData())`, and bounded `DoubleEndedQueue.Bytes32Deque` `popFront` / `popBack` `while` loops (`Governor._checkGovernance`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `Create2.computeAddress(bytes32, bytes32, address)` and `Create2.computeAddress(bytes32, bytes32)` (`lowerYulPrefixKeccakBlock?`) | Recognizes the 7-statement Yul block `let ptr := mload(0x40); mstore(add(ptr, 0x40), bytecodeHash); mstore(add(ptr, 0x20), salt); mstore(ptr, deployer); let start := add(ptr, 0x0b); mstore8(start, 0xff); addr := and(keccak256(start, 85), 0xffffffffffffffffffffffffffffffffffffffff)` and lowers it to 3 word-aligned 32-byte writes at `ptr = mload(64)` (`word0 = (prefixByte << 248) \| ((deployer & (2^160 - 1)) << 88) \| (salt >> 168)`, `word1 = (salt << 88) \| (bytecodeHash >> 168)`, `word2 = bytecodeHash << 88`) followed by `keccak256(ptr, 85)` and the target assignment. Mismatched offsets, prefix widths, or hash lengths fail closed. |
| `Clones.predictDeterministicAddress(address, bytes32, address)` and `Clones.predictDeterministicAddress(address, bytes32)` (`lowerYulPrefixKeccakBlock?`) | Recognizes the 8-statement Yul block `let ptr := mload(0x40); mstore(add(ptr, 0x38), deployer); mstore(add(ptr, 0x24), 0x5af43d82803e903d91602b57fd5bf3ff); mstore(add(ptr, 0x14), implementation); mstore(ptr, 0x3d602d80600a3d3981f3363d3d373d3d3d363d73); mstore(add(ptr, 0x58), salt); mstore(add(ptr, 0x78), keccak256(add(ptr, 0x0c), 0x37)); predicted := and(keccak256(add(ptr, 0x43), 0x55), 0xffffffffffffffffffffffffffffffffffffffff)`, packing the 55-byte EIP-1167 creation code into 2 aligned words at `ptr` and `ptr + 32`, binding `initHash := keccak256(ptr, 55)`, packing the 85-byte CREATE2 preimage into 3 aligned words at `ptr + 64`, `ptr + 96`, and `ptr + 128`, and evaluating `keccak256(ptr + 64, 85)`. |
| `keccak256(_msgData())` and zero-argument `bytes calldata` / `bytes memory` `msg.data` helpers (`lowerMsgDataBuffer`, `lowerEncodedBytes`, `lowerStringHelperStmts`) | `lowerEncodedBytes` and `lowerStringHelperStmts` accept zero-argument internal/private/public helper calls returning `bytes calldata` or `bytes memory` whose single `return` expression resolves to `msg.data` (via `inlineMsgDataFn`), materializing the full `calldatasize`-byte transaction calldata (selector word plus calldata words) into an aligned memory buffer via `lowerMsgDataBuffer` while keeping direct `keccak256(msg.data)` rejected at `msg.data`. |
| Bounded-range pop `while` loops such as `DoubleEndedQueue.Bytes32Deque` `popFront` / `popBack` (`while (_governanceCall.popFront() != msgDataHash) {}`, `Governor._checkGovernance`, `lowerWhile`, `boundedRangePopBounds?`) | `lowerWhile` recognizes `while (q.pop() != target) {}` (the call on either side of `!=`) when `pop` is a 1-argument storage helper over a struct of two `uint128` bounds and one `mapping(uint128 => bytes32)` (any helper, struct, and member names) whose body is structurally a range pop: `uint128 i = q.lo; if (i == q.hi) revert ...; value = q.data[i]; [delete q.data[i];] q.lo = i + 1;` (low end) or `uint128 i = q.hi; if (i == q.lo) revert ...; --i; value = q.data[i]; [delete q.data[i];] q.hi = i;` (high end). The low/high bound members are derived from that body. `q` must resolve to a storage path with an empty key prelude, `target` is a pure/stateless `bytes32` expression (`!statefulCallIn target && !assignmentIn target`), and the loop body is empty (`bodyStmts.isEmpty`). Lowers to `bound := ((hi - lo) & (2^128 - 1)) + 1`, `done := 0`, and `Stmt.forEach loopVar bound [ite (done == 0) (popPre ++ targetPre ++ [ite (popVal == targetVal) [done := 1] []]) []]`, so matching elements terminate the loop and missing elements pop until `lo == hi` and revert (e.g. `QueueEmpty()`) on the `(len + 1)`-th iteration. Helpers without the empty-range revert or bound advance are not recognized; non-empty loop bodies or stateful/non-`bytes32` targets fail closed with located diagnostics. |

### Development slice: `bytes calldata` / `msg.data` slices (`data[start:end]`), `Governor._isValidDescriptionForProposer` (unaligned Yul tail `mload`, `bytes` element reads, bounded tail-window `for` loops), `bytes1`–`bytes31` locals/helpers/casts (`bytes12`, `bytes20`, `ERC2771Context`), and `MemberAccess` tuple assignments (`AccessManager`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `bytes calldata` and `msg.data` / `_msgData()` slices (`data[start:end]`, `data[start:]`, `data[:end]`, `data[:]`, `lowerCalldataSlice?`) | `lowerCalldataSlice?` recognizes `IndexRangeAccess` on unshadowed `bytes calldata` parameters (`calldataBytes` with `inMemory == false`), direct `msg.data`, and zero-argument `bytes calldata` helpers returning `msg.data` (`_msgData()`). Evaluates optional unsigned `start` (default `0`) and `end` (default `base.length`) bounds once, enforces `start <= end` and `end <= base.length` (reverting with empty returndata on out-of-bounds slices, matching `solc`), and yields `(slicePre, baseOffset + start, end - start, isMsgData)`. Supported in `.length` (`MemberAccess`), `bytesN(slice)` casts (`1 <= N <= 32` via `lowerBytesToFixedBytes`, stitching the 4-byte selector word and calldata payload when `isMsgData` and `offset < 4`), `abi.decode(slice, (...))` (`lowerAbiDecodeItems`, when `!isMsgData`), and memory materialization (`lowerEncodedBytes`, copying `len` bytes into an aligned memory buffer for `bytes(slice)`, `keccak256(slice)`, `abi.encode*`, and `bytes.concat`). Signed slice bounds or `IndexRangeAccess` on `memory` / `storage` arrays fail closed. |
| `Governor._isValidDescriptionForProposer`: unaligned Yul byte-buffer tail `mload(add(buf, sub(len, k)))`, dynamic `bytes` / `bytes(string)` element reads `b[i]`, and bounded tail-window `for (uint256 i = len - K; i < len; ++i)` loops | In `yulByteBufferLoad?`, `mload(add(buf, sub(lhs, k)))` (and `mload(add(sub(lhs, k), buf))`) on a headerless `EncodedBytes` buffer (`yulByteBufferByName?`) with literal `1 <= k <= 32` computes `addr := buf.pointer + (lhs - (32 + k))` and reconstructs the unaligned 32-byte word from the two surrounding aligned words (`(mload(addr & ~31) << (8 * (addr & 31))) \| (mload((addr & ~31) + 32) >> (256 - 8 * (addr & 31)))`); `k == 0` or `k > 32` fails closed (`unsupported Yul builtin mload`). In `lowerExpr`, `IndexAccess` `b[idx]` on dynamic `bytes` (`bytes memory`, `bytes calldata`, `bytes storage`, `bytes(str)`) evaluates `buf ← lowerEncodedBytes b`, checks `idx < buf.size` (`Panic(0x32)`), and loads the single byte at `buf.pointer + idx` as a left-aligned `bytes1` word (`shl 248 (byte (addr & 31) (mload (addr & ~31)))`). `lowerFor` and `lowerHelperFrom` support `for (uint256 i = bound - K; i < bound; ++i)` (`1 <= K <= 256` literal, `bound` invariant), running `K` iterations with `i := (bound - K) + iterIdx` (including early `if (...) return ...;` inside single-return helpers). |
| Narrow fixed-bytes (`bytes1`–`bytes31`) locals, helper parameters/returns, `bytesN("...")` string literal casts (`N < 32`), and `bytes12` / `bytes20` integer/address conversions (`ERC2771Context._msgSender()`, `Votes`) | `localParamType`, `cleanHelperResultExpr`, and `lowerYulDirectAssignmentTarget` support `bytes1`–`bytes31` (`ParamType.bytesN w`, left-aligned to `256 - 8*w` bits), while keeping root ABI parameters and storage fields restricted to `bytes4` and `bytes32`. `lowerCast` supports `bytesN("...")` / `bytesN(hex"...")` for `1 <= N < 32` when the literal byte length is `<= N` (leaving `bytes32("...")` rejected), `bytesN(bytesSliceOrMemory)` (`1 <= N <= 32`), `bytes12(uint96)` / `uint96(bytes12)` (`shl 160` / `shr 160`), `bytes20(uint160)` / `uint160(bytes20)` / `bytes20(address)` / `address(bytes20)` (`shl 96` / `shr 96`), and widening/truncating conversions between `bytes12` / `bytes20` and `bytes32`. `lowerBinary` supports `==`, `!=`, `<`, `<=`, `>`, `>=`, `&`, `\|`, and `^` on matching `bytesN` types (rejecting implicit `int_const` operands), and `AbiEncoding` packs `bytes1`–`bytes32` values by their exact byte width (`scalarPackedWidth`). |
| Tuple assignment with `MemberAccess` storage or flat-struct targets (`(_roles[roleId].grantDelay, effect) = _roles[roleId].grantDelay.withUpdate(...)`, `AccessManager`) | `lowerEffect` `TupleExpression` assignment supports `MemberAccess` components alongside `Identifier` components, resolving each `MemberAccess` target against flat `memory` struct locals (`flatStructs`), ERC-7201 raw-slot storage structs (`SPath.rawSlot`), and top-level or 1-/2-/3-key mapping-backed storage structs (`SPath.zero`, `SPath.one`, `SPath.two`) with boolean `0`/`1` normalization and key-capture prelude validation. |

### Development slice: `mapping(bytes4 => ...)` in storage structs and top-level/nested mappings, `bytes4[]` parameters and `abi.decode(..., (bytes4[]))`, `bytes calldata` helper arguments and slices (`AccessManager`), `bytes1` ABI parameters/returns, and `bytes4`/`bytes1` event parameters

| Supported Solidity | Lowering boundary |
| --- | --- |
| `mapping(bytes4 => ...)` in storage structs and top-level/nested/3-key mappings (`AccessManager.TargetConfig.allowedRoles`, `_targets[target].allowedRoles[selector]`, `AccessManager.getTargetFunctionRole`, `AccessManager.canCall`) | `mappingKey` accepts `bytes4` (`Some .bytes32` in the 256-bit storage key model, left-aligned in the upper 4 bytes), enabling `bytes4` keys in top-level 1-/2-/3-key mappings (`mappingSpine`), struct-member 1-/2-key mappings (`decodeStructLayoutMembers`), and ERC-7201 raw-slot struct mappings (`resolveRawStructInfo`). `lowerRef` converts `IndexAccess` keys on `mapping(bytes4 => ...)` bases via `convert "bytes4"`, and `computeSPathBaseSlot`, `computeNestedMappingSlot`, and `computeStructMappingLeafSlot` left-align `bytes4` keys (`k` in upper 32 bits, lower 224 bits zeroed) when hashing `keccak256(abi.encode(k, slot))`, matching `solc` storage slot layout. |
| `bytes4[]` calldata/memory parameters, locals, helper arguments, and `abi.decode(..., (bytes4[]))` (`AccessManager.setTargetFunctionRole`) | `scalarArrayElement?` accepts `bytes4[]` (`(.uint256, .uintN 256)`). Calldata `bytes4[]` indexing in `lowerRef`, calldata-to-memory materialization in `AbiLowering.scalarArrayMemoryHead` and `AbiLowering.materializeScalarArray`, and `abi.decode(..., (bytes4[]))` in `abiDecodeScalarGuard?` enforce right-padding (`bitAnd word (2^224 - 1) == 0`, reverting with empty returndata on dirty lower 224 bits). `lowerLocal` and `lowerEffect` convert `bytes4` element reads and writes on `bytes4[]` memory arrays. |
| `bytes calldata` helper arguments (`_canCallExtended(caller, data)`, `_getAdminRestrictions(_msgData())`) and slices on helper `bytes calldata` parameters (`data[0:4]`, `data[0x04:0x24]`, `data[0x24:0x44]`) | `lowerCallArgs` and `bindHelperParams` allow passing `bytes calldata` expressions (`_msgData()`, `msg.data`, `data[start:end]`, or `bytes calldata` parameters) to `bytes calldata` helper parameters (`CallArg.byteBuffer` / `CallArg.calldataBytes`). `lowerCalldataSlice?` returns `(slicePre, offsetExpr, lenExpr, fromCalldata, isMsgData)` and admits unshadowed `bytes calldata` helper parameters bound in `byteBuffers` or `calldataBytes` (`inMemory == true`), routing `bytesN(slice)` (`lowerBytesToFixedBytes`), `abi.decode(slice, (...))` (`lowerAbiDecodeDataSource`), and `lowerEncodedBytes` through `readAbiDecodeWord fromCalldata` (`calldataload` when `fromCalldata == true`, unaligned-safe `mload` reconstruction when `fromCalldata == false`). |
| `bytes1` root/helper parameters, returns, `abi.decode(..., (bytes1))`, `abi.encode*`, and `bytes.concat` (`Strings.tryHexToUint(bytes1)`) | `paramType` maps `"bytes1"` to `ParamType.bytesN 1` (`TransactionAccess` and `SequenceRunner` decode/encode `bytesN 1` as left-aligned `v * 2^248` with lower 248 bits zeroed). `importSlice` and `abiDecodeScalarGuard?` guard `bitAnd word (2^248 - 1) == 0` on calldata and `abi.decode` inputs; `cleanHelperResultExpr` masks `bytes1` returns to the top byte; and `lowerPackedArgument` (`abi.encodePacked`, `bytes.concat`) writes 1-byte `bytes1` payloads directly from the left-aligned word without shifting. |
| `bytes4` and `bytes1` event parameters (`event TargetFunctionRoleUpdated(address indexed target, bytes4 selector, uint64 indexed roleId)`) | `lowerEmit` and `SequenceRunner.observeEventValue` accept `.bytesN 4` and `.bytesN 1` event parameters when the argument is a matching direct root parameter reference (`.param _`, matching `Compiler.CompilationModel.ValidationEvents`), masking observed topic/data words to their upper 32 or 8 bits (`value - value % 2^(256 - 8*w)`). Non-parameter `bytes4` / `bytes1` event expressions fail closed (`narrow event arguments currently require a matching direct parameter`). |
### Development slice: SSTORE2-style `create2` code storage and struct event parameters

| Supported Solidity | Lowering boundary |
| --- | --- |
| `bytes memory code = abi.encodePacked(PREFIX, abi.encode(s)); assembly { addr := create2(0, add(code, 0x20), mload(code), salt) }` in roots and inlined library/internal helpers (`lowerYulCreate2?`, `lowerYulValue`) | `startsWithInitcodeTemplate` records a `bytes memory` local when its initializer is `abi.encodePacked` / `bytes.concat` whose first argument is a hex literal or hex constant accepted by `DenoteCreate2.templateCost` (inspected bytes; currently the 11-byte `PUSH0` and 13-byte `PUSH1 0` copy-and-return prefixes) and it is never reassigned. `create2` must be the whole value of a Yul assignment or `let`; the value must be the literal `0`, the offset `add(buf, 0x20)` / `add(0x20, buf)` and the size `mload(buf)` of the same local. It lowers to `Stmt.ecm (SolidityCreate2.module r) [0, buf.pointer, buf.size, salt]` and the expression `r & (2^160 - 1)`. `Denote.executeByteCreate2` reads the initcode from physical memory through `Create2Opcode.execute` (parent gas from `ByteCallEnvironment.gas`, Keccak through the model oracle), binds the address or zero, installs the expanded memory and commits the account transition; parent out-of-gas and static/size aborts halt with empty data, and unchecked initcode or missing gas is a payload-free instrumentation `.revert`. Functions whose only CEI barriers or reentrancy windows are these closed transports carry the unchecked obligations `solidity_closed_transport_cei` / `solidity_create2_initcode_reentrancy`. |
| `emit E(S s, bytes32 indexed id, ...)` with non-indexed struct parameters (`lowerStructEmit`) | Events with a struct-typed parameter take this path; scalar-only events keep `Stmt.emit`. Non-indexed arguments are memory struct identifiers (dynamic or static ABI schema) or scalars, encoded by the shared `lowerAbiEncodeArgs` (`abi.encode` lowering). Indexed parameters must be total `uint*` / `address` / `bool` / `bytes32` expressions, cleaned with `cleanHelperResultExpr`. Topic 0 is the declaration's `eventSelector`. The statement is `Stmt.ecm (SolidityLog.module E n) (topics ++ [ptr, size])`; `Denote.executeByteLog` records the topics as `indexedArgs` and the payload words as `args` and rejects non-word payloads as instrumentation errors. The sequence adapter reports such logs byte-exactly. |

Validation: `check_create2_struct_emit.py` replays the fixture and its `renamed` and `expanded` variants on source EVM, Denote and the compiled model. Deployment accounts are discovered from both EVM routes' CREATE2 opcode traces (`deployment.py`), and code, nonces and balances of every planned account, the caller's nonce, return data, storage and exact logs are compared; payloads stay small because Denote's closure-based physical memory makes byte copies quadratic in time. `check_create2_struct_emit_rejections.py` pins 17 located near-miss rejections and 8 positive controls, and `check_create2_struct_emit_mutations.py` holds ten runtime importer/Denote mutants and four admission-guard mutants.

### Development slice: `<address>.code.length` and optional-bool low-level calls

| Supported Solidity | Lowering boundary |
| --- | --- |
| `require(token.code.length > 0, NoCode());` and other `<addr>.code.length` reads on `address`-typed accounts (`lowerExtCodeSize`) | The account expression is lowered to an atom and read by `Stmt.ecm (SolidityExtCodeSize.module r) [addr]`, compiled to `let r := extcodesize(addr)`. `Denote.executeByteExtCodeSize` binds `DenoteExternalCode.extCodeSize world (Address.ofNat addr)` (`executeByteExtCodeSize_eq`); the legacy `Expr.extcodesize` and its `ContractState.codeSize` view are unchanged. `address(this).code.length` rejects because the executing contract's code differs between the source and compiled routes. The transport hands control to no account, so `eraseClosedTransports` erases it for the CEI check. |
| `(bool success, bytes memory returndata) = token.call(abi.encodeCall(IERC20.transfer, (to, amount)));` followed by the returndata-forwarding `if` and the optional-bool `require` (`lowerLowLevelCallSequence?`, hooked into `lowerRootStatements` and `lowerVoidHelperFrom`) | The three statements are matched structurally (`lowLevelCallMember?`, `isReturndataForwarding`, `isOptionalBoolValidation`, `lowLevelEncodeCallParts`); `success` and `returndata` may not be referenced elsewhere (`jsonMentionsDecl`). The receiver and encoded arguments are lowered in source order (stateful operands reject), converted to the function's parameter types, and emitted as `Stmt.ecm (SolidityLowLevelCall.optionalBoolModule r selector n) (target :: words)` followed by the `require`'s own `reason` on `r` (`lowerRequireWith`). `Denote.executeByteOptionalBoolCall` prepares the calldata with `prepareByteWordCall .call` (free pointer advanced after the call), runs `ByteExternalCall.executeChecked`, and dispatches on `classifyOptionalBoolCall`: forward the child's bytes, revert empty on malformed returndata, or bind the decoded word. `DenoteLowLevelCall` proves the request is `callBytesRequest` and that the result is `1` exactly when `decodeOptionalBoolCall` accepts. Functions whose reentrancy windows are only these calls, after which no storage is read or written and nothing is logged, carry `reentrancyTrusted` with the unchecked obligation `solidity_trailing_low_level_call_reentrancy`; storage reads, writes and logs after them carry `solidity_post_call_state_access` instead (*Post-CALL storage access and logs*). |

Validation: `check_external_code_and_low_level_call.py` replays the fixture and its `renamed` and `expanded` variants on source EVM, Denote and the compiled model against eleven `RecordingCallResponder` configurations (true, false, empty, invalid and short words, extra bytes, short/empty/long revert payloads), an account without code and the sender EOA; responders record the call count, calldata size and first four calldata words, so selector, argument encoding and committed callee writes are compared in storage. Denote receives the responders' deployed runtime code for code-length reads. `check_external_code_and_low_level_call_rejections.py` pins 19 located near-miss rejections and 7 positive controls, and `check_external_code_and_low_level_call_mutations.py` holds ten runtime importer/Denote/ECM mutants and five admission-guard mutants.

### Post-CALL storage access and logs

| Construct | Lowering and admission |
|---|---|
| Storage reads, storage writes and `emit` after a closed value-free `CALL` (typed void interface calls, their `try` clauses and continuation, and the optional-bool low-level call) | The post-call statements lower exactly as they do anywhere else; nothing is cached across the call. Denote runs them against the world the callee's response committed (`ByteExternalCall.Response.commit`), which an unconstrained adversary chooses freely, including by re-entering any entrypoint, so every post-call `SLOAD` observes the callee's writes and every log follows the callee's logs, as on the EVM. A function is admitted when every CEI barrier and reentrancy window of its body is a closed transport (`onlyClosedCallStateWindows`: erasing the closed transports and closed `CALL`s, `eraseClosedInteractions`, leaves a CEI-clean body with no reentrancy window); an internal call, a non-closed external call or any other call module after the `CALL` keeps it out with the located message *storage reads, storage writes and logs after an external CALL are supported only when every external interaction of the function is a closed transport*. Admitted functions carry `reentrancyTrusted`, `allowPostInteractionWrites` when the unerased body violates CEI, and the unchecked obligation `solidity_post_call_state_access`: the source has no reentrancy guard, so a proof about such a function must assume a callee hypothesis (`Denote.CallKeepsCallerStorage`, `Verity/Core/Model/ByteCallStorageFrames.lean`, under which a post-call read sees the pre-call word) or account for re-entry (`ReentrantCallees`). Code-hash reads after the call still reject (`codeHashesAfterChange`). |

Validation: `PostCallStateAccessChecks.lean` pins the trust flags of `PostCallStateAccess.sol` (`SyntheticPostCallWrite`, `SyntheticCallbackTransfer`, `SyntheticPostCallEvent`; via-IR and legacy) and runs them in Denote against an inert callee, a failing callee, an account without code and a callee that calls back into the contract once: the callback's writes are visible to the caller's post-call reads, a re-entrant spend of the same credit makes the caller's post-call checked subtraction panic (`0x11`) and roll back, a re-entrant double spend with enough credit succeeds, and a callback's log precedes the caller's. It also pins the admission classifier on hand-built bodies. `check_post_call_state_access.py` runs each contract's A/B/C sequence (source EVM on Anvil, Denote, compiled model) against the recording call responders, an account without code and the sender EOA. The post-CALL cases of `check_interface_static_call_rejections.py` and `check_extcodehash_rejections.py` are positive controls.

### Development slice: address immutables without an inline initializer

Before this slice, every address immutable without an inline initializer read
as `address(this)` once a contract had more than one state variable, so an
immutable assigned from a constructor argument silently became the contract's
own address. Such an immutable is now `Expr.immutable NAME`, declared in
`model.immutables` and installed by a synthesized constructor from its
argument; only an exactly-once, top-level `x = address(this)` keeps the
`address(this)` binding (Uniswap v4's `NoDelegateCall.original`, whose
PoolManager import this rule leaves unchanged). `check_immutable_lowering.py` pins the
lowering of eight cases, including conditional, repeated, indirect and
inherited assignments.

### Development slice: immutables of every value type and inline initializers

The binding generalizes from address immutables to every value type except
enums and function types, and covers inline initializers. A constructor write
of any shape keeps the immutable an argument of its own type; an unwritten
immutable whose initializer reads the deployment environment is installed by
the synthesized constructor; an unwritten immutable whose value the source
fixes (no initializer, or literals only) reads as that value; public getters
return the binding. Writes count wherever solc accepts them, `++` and `--`
included: in constructors, in any state variable's initializer and in
inheritance-specifier arguments. Nothing picks a value a deployment might not
have: an initializer that reads an immutable (it runs before the constructors),
every other initializer that does not lower to literals and the environment,
and enum and function-typed immutables keep the located rejection.
`check_immutable_lowering.py` adds cases for each binding, the argument types,
the literal values, each write form and place, and the rejections;
`ImmutableScalarSequence` is the A/B/C fixture; mutants
`import-immutable-scalar-installed-zero`, `-argument-shift`,
`-initializer-zero`, `-argument-uncleaned`, `-increment-unwritten` and
`-initializer-write-missed`.

### Development slice: `<address>.code` and dynamic-struct `abi.decode` returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| `abi.decode(pointer.code, (S))` and `bytes memory data = pointer.code;` on `address`-typed accounts (`lowerExtCodeCopy`, hooked into `lowerAbiDecodeDataSource` and the `bytes memory` local initializer) | The account is lowered to an atom and copied by `Stmt.ecm (SolidityExtCodeCopy.module r) [account]`; the buffer's data pointer `r + 32` and length `mload(r)` are bound. The compiled transport is solc's `external_code_at`: `extcodesize`, allocation of `roundUp(size) + 32` bytes at the free pointer (`Panic(0x41)` when the length or new free pointer exceeds 64 bits or wraps), the length word, then `extcodecopy(account, r + 32, 0, size)`. `Denote.executeByteExtCodeCopy` performs the same writes on physical memory from `DenoteExternalCode.accountCode` (address taken modulo `2^160`). `address(this).code` rejects because the executing contract's code differs between the source and compiled routes; `.code` keeps its located rejection everywhere else (`keccak256(a.code)`, `a.code[i]`). The transport hands control to no account, so `eraseClosedTransports` erases it for the CEI check. |
| `abi.decode(data, (S))` of a struct with dynamic array members from a `bytes memory` buffer (`parseAbiDecodeItem` → `AbiDecodeTypeItem.dynamicStruct`, `AbiMemoryDecode.materialize`) | Only structs that are not flat and whose complete `AbiSchema` contains unsigned scalars, dynamic arrays of unsigned scalars and dynamic arrays of flat scalar structs take this path; every other member keeps the existing `unsupported abi.decode struct member type` diagnostic. The decoder follows solc's `abi_decode_tuple_*_fromMemory`: one head word, the struct offset (`≤ 2^64 - 1`), a signed remaining-size check for the struct head, eager allocation, then members in declaration order: scalars are validated (`validator_revert_*`), arrays check their offset, `slt(header + 31, end)`, `Panic(0x41)` for lengths or allocations beyond 64 bits before the payload bound `data + length * elementSize ≤ end`, and flat-struct elements are separately allocated with their own remaining-size check. The result is a memory `MemParam` with the complete schema, so field reads and `abi.encode` use the existing memory-struct lowering. Calldata sources and additional decode targets reject. |
| `function f(...) external view returns (S memory) { return abi.decode(pointer.code, (S)); }`, `S memory s = abi.decode(...); return s;` and `return param;` for `S memory` parameters (`functionDynamicStructReturn?`, `lowerDynamicStructReturnValue`) | The model return type is `AbiSchema.paramType S`. The returned struct is encoded by `lowerEncodedMem` (the root-tuple branch of `abi.encode`) and returned by `Stmt.ecm SolidityReturnMemory.module [ptr, size]`, compiled to `return(ptr, size)`; `Denote.executeByteReturnMemory` stops with the buffer's words in `observedReturnWords` (non-word buffers are instrumentation errors). An unreachable `Stmt.revertEmpty` follows the transport because `Stmt.ecm` metadata cannot state termination for the compiler's exhaustive return analysis. Named returns, calldata structs, helper calls and other expressions reject. |

Validation: `check_extcodecopy_struct_decode.py` replays the fixture and its `renamed` and `expanded` (`bytes memory` local, decoded local plus `return`, memory alias) variants on source EVM, Denote and the compiled model. Code is stored by the checked CREATE2 transport, from canonical encodings and from 22 raw payloads around every decoder check (non-canonical, shared and backwards offsets, trailing bytes, dirty scalars, truncated heads and payloads, offsets beyond 64 bits, `Panic(0x41)` lengths and allocations, empty and short code), then read back by `load` (return of `abi.decode(pointer.code, (Spec))`), `summary` (field reads) and `echo` (memory parameter return); deployment accounts come from EVM CREATE2 traces. `check_extcodecopy_struct_decode_rejections.py` pins 14 located near-miss rejections and 8 positive controls, and `check_extcodecopy_struct_decode_mutations.py` holds 17 runtime importer/decoder/Denote/ECM mutants and five admission-guard mutants.

### Development slice: `<address>.codehash`

| Supported Solidity | Lowering boundary |
| --- | --- |
| `if (helper.codehash != EXPECTED) revert BadHelper();` and other `<addr>.codehash` reads on `address`-typed accounts (`lowerExtCodeHash`) | The account expression is lowered to an atom and read by `Stmt.ecm (SolidityExtCodeHash.module r) [addr]`, compiled to `let r := extcodehash(addr)`; the result is a `bytes32` word. `Denote.executeByteExtCodeHash` binds `DenoteExternalCode.extCodeHash (oracleBytesHash oracle) world (Address.ofNat addr)` (`executeByteExtCodeHash_eq`): `0` when `accountEmpty` (EIP-161: nonce `0`, balance `0`, no code; storage does not count), otherwise the model Keccak oracle over the runtime code, so an existing account without code yields `keccak256("")`. `address(this).codehash` rejects because the executing contract's code differs between the source and compiled routes; so does a read whose lowered operand may be the executing contract (`lowerCodeReadTarget` / `checkCodeReadTargets`: a local, helper or modifier parameter, tuple component, conditional result or inlined helper result bound or assigned `address(this)` anywhere in the root, directly or through another such binding; the marks are a fixpoint over the whole lowered root body), and the same rule guards `code.length` and `code`. The transport hands control to no account, so `eraseClosedTransports` erases it for the CEI check; a read that runs after a low-level call or `create2` in program order rejects (`codeHashesAfterChange`), because the call can make an empty account exist. |

Validation: `check_extcodehash.py` replays the fixture and its `renamed` and `expanded` (codehash bound to locals, `!=` / `==` rewritten through `!`) variants on source EVM, Denote and the compiled model. Probed accounts: three accounts deployed from raw initcode (the bound runtime `0x5f5ff3`, a one-byte code and a 77-byte code), an account deployed from initcode that returns empty runtime code (nonce 1, no balance, no code), the deployer EOA (nonce > 0), anvil's second prefunded EOA (nonce 0), a never-touched address and the `0x01` precompile (empty on anvil, so `0`). Denote receives the coded accounts' runtime code (`accountCode`), the EOAs' genesis balance (`accountBalance`) and the created account's nonce (`foreignNonce`); the campaign requires all five code-hash values (three code hashes, `keccak256("")`, `0`) to be observed, and `keccak256("")` for the nonce-only account. `check_extcodehash_rejections.py` pins nine positive controls and thirteen located rejections (among them `address(this)` through a local, a reassignment, a chain of locals, a helper parameter, a conditional, a helper's branch return, a tuple declaration, a loop-carried assignment, and the `code.length` alias; a positive control reuses an alias name in a second root). Mutants: `import-code-hash-as-code-size`, `import-code-hash-target`, `denote-code-hash-empty-account` (`keccak256("")` for empty accounts), `denote-code-hash-existence` (balance ignored), `denote-code-hash-nonce` (nonce ignored), `import-code-hash-eq-iszero` (`!=` lowered to `eq` instead of `iszero(eq)`), `ecm-code-hash-opcode`, and the admission mutants `import-code-hash-this-guard`, `import-code-read-self-alias` (the lowered-operand guard) and `import-code-hash-after-call-guard` (a read after a call).

# Initcode execution groundwork

`Verity/Core/Model/InitCodeExecution.lean` executes the bytecode instructions in
the eleven-byte SSTORE2 deployment prefix with an explicit instruction bound.
The kernel proof `push11CopyReturn_returns_payload` composes nine intermediate
instruction lemmas and proves that the returned bytes equal the appended
payload. Byte-copy frame lemmas preserve reads outside the destination range.
This is deployment proof infrastructure: it adds no supported Solidity or Yul
construct by itself. The SSTORE2-style `create2` row above admits Yul `create2`
only over `bytes memory` buffers that start with these checked templates.

The account-world prerequisite now stores bounded nonces, balances, exact code
bytes and finite storage in `ContractState.accountWorld`. `DenoteCreate2`
executes the checked initcode templates and handles transfers, nonce increments,
collisions, deposit rules and child gas. Account frames and existing transaction
rollback include this metadata. The source-storage/account-storage bridge,
parent opcode charging, ABI/events, compiled-model route and importer lowering
remain required before CREATE2 is supported. Unsupported initcode is an
instrument error, never a fabricated successful deployment or Solidity revert.

`BytesObjectMemory` provides a byte-level immutable object representation:
big-endian length header, payload at base+32, zero padding and disjoint-write
frame proofs. Its EVM/Lean instrument observes source-created objects and
aliases after another allocation. This is a prerequisite, not new supported
Solidity: allocator/pointer identity, overflow and gas behavior, declaration
provenance, the canonical word-memory bridge and compiled-model integration
remain mandatory before admitting object-pointer Yul expressions.


### Development slice: static nested sub-structs in flat memory structs (#2738)

| Supported Solidity | Lowering boundary |
| --- | --- |
| A static struct member of a flat memory struct (`struct O { I inner; uint128 idx; }`) as a root return (named or unnamed), positional or named constructor argument, member read or write (`o.inner.x = v`), whole sub-struct assignment from a fresh value (`o.inner = I(v)`), `delete o.inner`, and helper argument | `flatStructLeaves?` flattens it into leaves named `member.leaf`; solc ABI-encodes a static nested struct inline, so the leaves are the returned words in order. `o.inner` is a view over the same leaf bindings (a by-reference parent makes the view by-reference). Constructor leaves are snapshotted as they are evaluated (`S(k, ++k)`), and legacy (`viaIR := false`) evaluates named constructor arguments in declaration order, as solc. |
| Rejected | `enum` leaves, nested structs in helper results, `S memory s;` without an initializer when `S` has a struct member (`uninitialized nested struct locals are outside this slice`), raw Yul `keccak256` over a flattened nested struct (`raw memory hash of a flattened nested struct is outside this slice`), and every way solc would share the sub-struct's pointer: assigning a memory struct local to `o.m` (`memory struct local aliasing is outside this slice`), `I memory i = o.m`, returning `p.m` of a memory struct parameter, and member writes through it in a helper. |

`NestedMemoryStructReturnSequence` (`nested-memory-struct-return`) runs A/B/C variants `baseline`, `renamed` (locals) and `members-renamed` (struct members, types, helpers and state variables): a nested struct root return built member by member, by `delete` and by whole assignment, a helper reading nested leaves, constructor leaves snapshotted across `++k` arguments (`nestedOrder`), and narrow nested leaves written from assembly-dirtied words (`snapshot`).

### Development slice: `S[] memory` through internal helpers (#2721)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `S[] memory` of a struct whose members are unsigned scalars, `address`, `bool` or `bytes32`: `new S[](n)`, `S[] memory x;`, element reads `a[i].m`, element writes `a[i].m = v`, `a[i] = S(...)` / `a[i] = b[j]`, `delete a[i]`, `S memory s = a[i]`, `a[i]` passed to an `S memory` helper parameter, and `S[]` helper parameters and results (named or unnamed, `return new S[](n)`) | The array reuses the `T[] memory` descriptor (`ScalarArrayParam` with `elemStructId`; `structMemArrayOf?` reads the element struct id from solc's `typeIdentifier`, never its name): each element word is a struct pointer, so the `T[]` lowerings that move pointers (helper arguments and results, reassignment, the `0x60` default) apply unchanged, and its `elementType` tag is not a Solidity type, so scalar conversions and encodings reject it. `new S[](n)` follows solc's `zero_complex_memory_array`: the array, then one distinct zeroed struct per element (`Panic(0x41)` guards). `a[i]` checks the bound (`Panic(0x32)`) and is a view of the element struct (`.abiElement` over a synthetic `structArray` root): member reads and writes reach its words, and `S memory s = a[i]` or an `S memory` helper parameter shares it. `a[i] = b[j]` stores the pointer; a constructor, a struct helper result or a storage struct is a fresh struct (members evaluated, then allocated); `delete a[i]` stores a fresh zeroed struct. The right-hand side is evaluated before the index, as solc. A root `S[] memory` parameter passes its pointer to an `S[]` helper parameter. |
| Rejected | `S[]` of structs with other members (`memory struct arrays require a struct whose members are unsigned scalars, address, bool or bytes32`), calldata `S[]` to memory, `S[]` in ABI encoding, hashing, events and root returns, raw Yul on the array pointer (`raw memory access to struct array pointers is outside this slice`, `raw memory reinterpretation of struct array pointers is outside this slice`), assigning a flat memory struct local to `a[i]` (`memory struct local aliasing is outside this slice`; solc would share its pointer), and returning a memory struct array element from a struct helper (`returning a memory struct array element (an alias) is outside this slice`). |

`StructMemoryArrayHelperSequence` (`struct-memory-array-helpers`) runs A/B/C variants `baseline`, `renamed` (locals) and `members-renamed` (struct members, types, helpers and state variables): the #2721 issue helpers (`_countHoldings(_holdings(a))`), a member-by-member fill of zeroed elements, writes through helpers and element aliases, distinct zeroed `new S[](n)` elements, element replacement and `delete a[i]`, assembly-dirtied narrow lengths, indices and members, and the `Panic(0x32)` paths. Mutants: `import-struct-memory-array-member-write`, `import-struct-memory-array-zeroed-elements`.

### CREATE2 parent opcode composition prerequisite

`Create2ParentGas` charges the Osaka base cost, six-gas Keccak and two-gas
EIP-3860 initcode words, and quadratic memory expansion. Zero-length ranges
do not expand memory. Kernel lemmas establish the EIP-150 gas split,
conservation and bounded child refunds. `Create2Opcode.execute` derives the
child allowance from parent gas, reads initcode from actual byte memory,
executes the concrete account transition and refunds unused child gas. The
expanded memory zero-extends inactive bytes; no backing-function contents
beyond the old active range become visible. Static/size violations abort,
parent out-of-gas aborts, and nonaligned instrument memory is rejected.

`check_deployment_world --parent-opcode` compares actual EVM opcode memory,
parent continuation gas, child allowance and account transitions against Lean,
including nonce-limit prechecks. It supplies neither initcode bytes nor a child
gas allowance to the Lean opcode driver. This remains A/B calibration, not an
imported or compiled-model C campaign. Canonical Stmt integration, complete
frame gas tracking, source allocator/memory refinement, account/storage bridge,
ABI/revert/event observations and all exact-head release gates remain required.
No new Solidity construct or whole-EVM equivalence is claimed here.


### Canonical flat-storage/account coherence

Concrete account storage uses `Std.TreeMap` with kernel-checked read-after-write
and outside-frame laws. `writePhysicalSlot`, `writePhysicalSlots` and
`modifyPhysicalSlots` update flat persistent storage and the self account's
finite storage together. Batch transformers read the original world, including
when targets alias. These APIs preserve code, nonce, balance, caller metadata,
transient keys and legacy shadow channels. Legacy `writeSlot` and bulk lenses
retain their previous account-world frame; their regression is unchanged.

Canonical Denote flat scalar, packed, mapping-word and fixed-array write helpers
use the physical APIs. The reference `SourceSemantics` uses the same exact
physical transitions; the statements of `DenoteAgreement` and
`DenoteFunctionAgreement` are unchanged. `AccountStorageBridge` proves coherence
for single/batch/transformed writes and runtime-code commits to another account.
Old shadow-mapping/channel-wide compatibility operations are not asserted to
preserve this relation and must not be used as an exact deployment bridge.

The scalar differential adapters initialize finite storage through the physical
API. The sequence adapter verifies flat/account agreement for every touched or
requested persistent slot after each transaction, including rollback. This
seeds storage only: it does not fabricate creator nonce, balance or code, model
external account effects, admit CREATE2, or establish full deployment A/B/C
equivalence. Those account inputs, complete gas/memory integration and the
remaining source-admission obligations still have to be implemented.

Stateful differential implementation snapshots bind the recorded Git HEAD to the campaign workspace and recheck it during replay. A commit switch with byte-identical sources still invalidates the campaign; an unavailable Git revision is an instrumentation error. This supplements source/artifact identity checks and does not certify unexecuted test phases.

### Regression evidence: `unchecked` blocks and tuple destructuring

`UncheckedSequence` and `TupleSequence` add stateful A/B/C fixtures for already
supported constructs: narrow `uint8`/`uint64` wrapping, unchecked mapping
decrements, `require` inside unchecked helper blocks, checked helpers called
from unchecked code, elided tuple components, conditional tuple selection,
literal tuple declarations, and multi-value root returns. An `unchecked` block
in a value helper may now contain a returning `if`: its statements are lowered
into the helper continuation followed by a synthetic block-end marker that
restores checked arithmetic and the name-keyed scope of the block's start
(`yulNames`, `yulMemoryArrays`, `yulMemoryStructs`), so a block-level
declaration is not visible to inline assembly after the block, which names the
outer local or constant it shadows; each `if` branch restores the lexical
`unchecked` flag. Block-level declarations are admitted whatever the
state-variable count (#2830; `UncheckedBlockDeclarationStateCountChecks`).
The same holds for an `if` in a value helper whose other branch returns:
the continuation is lowered inside the branch that falls through, after a
branch-end marker restoring the name-keyed scope of the `if`, so a declaration
in that branch does not shadow the outer local or constant for inline assembly
after the `if`. A plain block that a string or array helper flattens into its
continuation ends with the same marker (`HelperBranchScopeStateCountChecks`;
before, the assembly read the branch's or string helper block's declaration in
every contract).
Plain helper blocks with partial returns still reject with located
diagnostics. Each fixture has
metamorphic source variants (`check_storage --fixture unchecked-blocks` /
`tuple-destructuring`) and scheduled importer mutants
(`import-unchecked-block-*`, `import-tuple-destructuring-*`). Literal tuples on
the right of tuple assignments remain rejected.

Whole-contract frame proofs can use `Transactions.AdversarialEntryPointSequence` and `invariant_of_adversarial_entry_points` to vary both the transaction context and permitted oracle at each public call. Every permitted oracle must satisfy the actual per-entry-point execution obligation. The rule includes observed reverting frames through rollback; ABI decoding, dispatch and value transfers remain separate obligations. `adversarial_sequence_append` composes observed prefixes.

These frameworks run every entry point with `executeBody`'s default byte-call environment,
which has no adversary: an external call is then an instrumentation error, so no successful
step makes one, and an invariant proved through them says nothing about the transactions
that call out. `AllEntryPointsPreserveWith`, `CalleeEntryPointSequence` and
`invariant_of_callee_entry_points` choose the callees' behaviour too, at every step, among the
byte-call environments a predicate allows (a hypothesis about the callees, such as "they never
write the caller's storage"), and admit each step by its oracle, function and prepared world
(one fixed oracle for the whole sequence, or callers and calldata words from a given set);
`all_entry_points_preserve_with_of_success` and
`callee_sequence_append` are the counterparts of the rules above. `ReentrantCallees` lets
callees call back into the contract, a bounded number of levels deep: a successful answer is
then a nested sequence of the contract's own entry points from the call point
(`ReentrantEntryPointSequence`, with obligations `AllEntryPointsPreserveReentrant`), with the
caller's frame restored; `reentrant_answer_preserves` carries an invariant of the contract's
own storage through such an answer. Nested calls start from `beginReentrantFrame`, which keeps
the transaction's transient storage (EIP-1153): a callback reads what its caller stored there
and the caller reads what the callback left, so transient reentrancy locks and flags are
modelled as on the EVM. `EntryPointInvariantChecks` pins this: a callback from a frame with a
transient flag set writes where no fresh transaction can. Their steps also take ABI
decoding into account: each step's bindings decode its own world's calldata (`DecodedCall`,
through `Denote.bindExternalParams` as `denoteFunction` decodes), so a proof may use that a
`uint104` parameter is below `2^104`, no step runs a body on arguments no transaction can
pass, and a body with an explicit ABI prelude decodes the same calldata.
`Contracts/SolidityImportSmoke/EntryPointInvariantChecks.lean` uses each of them on a
three-entry model, including a step whose arguments decode from its frame.
