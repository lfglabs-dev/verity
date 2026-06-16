# External Call Modules (ECM)

External Call Modules are Verity's extension mechanism for external call patterns.
They replace the former hardcoded `Stmt` variants (`safeTransfer`, `callback`,
`ecrecover`, etc.) with a single generic `Stmt.ecm` variant backed by typed,
auditable Lean structures.

## Motivation

Verity's EDSL deliberately restricts raw external calls for safety. Every call
pattern must be explicitly known to the compiler. Before ECMs, adding a new
pattern (e.g., `safeApprove`, `permit`, Uniswap swaps) required modifying the
core `Stmt` inductive type and updating pattern matches across 11+ functions.

ECMs decouple call patterns from the compiler core. Standard patterns ship
in-tree under `Compiler/Modules/`. Third parties can publish their own as
separate Lean packages.

## Architecture

```
ExternalCallModule (Compiler/ECM.lean)
  ├── name : String
  ├── numArgs : Nat
  ├── resultVars : List String
  ├── writesState : Bool
  ├── readsState : Bool
  ├── compile : CompilationContext → List YulExpr → Except String (List YulStmt)
  ├── axioms : List String
  └── proofStatus : proved | assumed | unchecked

Stmt.ecm (mod : ExternalCallModule) (args : List Expr)
```

## Foreign Link Modes

Foreign dependencies must declare whether they are a deployed boundary or code
that becomes part of the generated artifact. Verity records this on every
`linked_externals` declaration and surfaces it in trust and assumption reports:

| Mode | Syntax | Use case | Artifact meaning |
|------|--------|----------|------------------|
| External ABI boundary | `linked_as := external` | Permit2, routers, verifier contracts, oracles | The dependency remains a real call boundary; adapters must preserve ABI return decoding and returndata bubbling. |
| Object-linked Yul | `linked_as := internal_yul` or `linked_as := object_linked` | Poseidon-style deterministic helpers and imported Yul libraries | Matching helper functions are injected into the runtime artifact from `--link` libraries. |
| Inline helper | `linked_as := inline` | Small pure helper bodies that a frontend/backend may inline | The helper remains visible as a foreign surface while the implementation is expected to be included at compile time. |
| Compiler runtime | `linked_as := compiler_runtime` | ABI/runtime helpers owned by the Verity compiler | The helper is part of the compiler-owned runtime surface, not a protocol deployment boundary. |

Omitting `linked_as` preserves the historical behavior and is equivalent to
`linked_as := internal_yul`.

Contracts compiled through the driver also emit one Yul comment per linked
external, for example `verity linked external PoseidonT3_hash
linkMode=objectLinked`, so the generated artifact carries the same mode
metadata as the trust reports. A dependency declared `linked_as := external`
must be lowered through an ABI-call ECM such as `Calls.withReturn`; raw
`externalCall` / `externalCallBind` helper lowering is rejected for that mode.

Source-level typed interfaces provide a higher-level wrapper over this same ECM
path:

```lean
interfaces
  interface IERC20 where
    function balanceOf(Address) view returns (Uint256)
  end

function readBalance (token : IERC20, owner : Address) : Uint256 := do
  let bal ← token.balanceOf owner
  return bal
```

The interface-typed parameter is ABI-encoded as `Address`. A bound `view` dot
call with one static ABI-word return emits
`Compiler.Modules.Oracle.typedReadWordSummaryModule`, which lowers to
`staticcall` and records a source-shaped oracle summary name such as
`IERC20.balanceOf` plus the exact ABI selector in trust reports. Non-`view`
single-return calls continue to use `Compiler.Modules.Calls.withReturnModule`
and select `call`. Interface methods with no `returns` clause lower to
`Compiler.Modules.Calls.noReturnModule` in statement position. Interface calls
currently support one return value and type-only interface parameter lists.

Typed-interface parameters are deliberately limited to static single-word ABI
values (`Uint256`, `Int256`, `Uint8`, `Uint16`, `Address`, `Bytes32`, `Bool`,
and newtypes over those values). Dynamic or composite parameter shapes such as
`Bytes`, `String`, arrays, tuples, and structs are rejected at elaboration time.
Those shapes need ABI-frame typed-interface lowering so calldata heads, dynamic
tails, and total sizes are encoded honestly; until that path exists, both
return-bearing and no-return typed-interface calls fail closed.

When the compiler encounters `Stmt.ecm mod args`, it:

1. Validates argument count matches `mod.numArgs`
2. Checks `mod.writesState`/`mod.readsState` against function mutability
3. Validates result variable scoping (no shadowing, no redeclaration)
4. Compiles each `Expr` argument to `YulExpr`
5. Calls `mod.compile ctx compiledArgs` to get `List YulStmt`
6. Injects the result

## Using ECMs in Contract Specs

```lean
import Compiler.Modules.ERC20
import Compiler.Modules.Precompiles

def vaultSpec : CompilationModel := {
  name := "Vault"
  fields := [{ name := "token", ty := .uint256 }]
  functions := [{
    name := "withdraw"
    params := [⟨"to", .address⟩, ⟨"amount", .uint256⟩]
    body := [
      Modules.ERC20.safeTransfer
        (Expr.storage "token")
        (Expr.param "to")
        (Expr.param "amount"),
      Stmt.stop
    ]
  }]
}
```

## Standard Modules

Standard modules ship in `Compiler/Modules/`:

| Module | Function | What it does | Axioms |
|--------|----------|--------------|--------|
| `ERC20.safeTransfer` | `transfer(to, amount)` | ERC-20 transfer with optional-bool-return handling: accepts exactly `true` or no returndata from a contract address | `erc20_transfer_interface` |
| `ERC20.safeTransferFrom` | `transferFrom(from, to, amount)` | ERC-20 transferFrom with optional-bool-return handling: accepts exactly `true` or no returndata from a contract address | `erc20_transferFrom_interface` |
| `ERC20.safeApprove` | `approve(spender, amount)` | ERC-20 approve with optional-bool-return handling: accepts exactly `true` or no returndata from a contract address | `erc20_approve_interface` |
| `ERC20.solmateSafeTransfer` | `transfer(to, amount)` | Solmate SafeTransferLib semantics: accepts no returndata or first returned word equal to `true` when `returndatasize() > 31` | `erc20_solmate_safe_transfer_interface` |
| `ERC20.solmateSafeTransferFrom` | `transferFrom(from, to, amount)` | Solmate SafeTransferLib semantics: accepts no returndata or first returned word equal to `true` when `returndatasize() > 31` | `erc20_solmate_safe_transferFrom_interface` |
| `Hashing.abiEncodeStaticWords` | Static-word `abi.encode` Keccak | Writes full 32-byte ABI words contiguously at the Solidity free-memory pointer and binds `keccak256(ptr, wordCount * 32)` | `keccak256_memory_slice_matches_evm`, `abi_standard_static_word_layout` |
| `Hashing.abiEncodePackedWords` / `Hashing.abiEncodePacked` | Static-word packed Keccak | Writes 32-byte words contiguously at the Solidity free-memory pointer and binds `keccak256(ptr, wordCount * 32)` | `keccak256_memory_slice_matches_evm`, `abi_packed_static_word_layout` |
| `Hashing.abiEncodeStaticArray` | Standard dynamic-array Keccak | Writes ABI head offset, binds array length once, writes contiguous fixed-width static elements, and hashes the ABI frame | `keccak256_memory_slice_matches_evm`, `abi_standard_dynamic_array_static_element_layout` |
| `Hashing.sha256PackedWords` / `Hashing.sha256Packed` | Static-word packed SHA-256 | Writes 32-byte words contiguously, calls precompile 0x02, and binds digest word | `evm_sha256_precompile`, `abi_packed_static_word_layout` |
| `Hashing.abiEncodePackedStaticSegments` | Static byte-width packed Keccak | Writes 1- to 32-byte static segments at byte-precise offsets from the Solidity free-memory pointer and binds `keccak256(ptr, totalBytes)` | `keccak256_memory_slice_matches_evm`, `abi_packed_static_segment_layout` |
| `Hashing.sha256PackedStaticSegments` | Static byte-width packed SHA-256 | Writes 1- to 32-byte static segments, calls precompile 0x02 over the exact byte length, and binds digest word | `evm_sha256_precompile`, `abi_packed_static_segment_layout` |
| `Hashing.eip712Digest` | EIP-712 digest | Writes `hex"1901"`, `domainSeparator`, and `structHash` to a 66-byte preimage and binds `keccak256(preimage)` | `keccak256_memory_slice_matches_evm`, `eip712_digest_layout` |
| `Precompiles.ecrecover` | Precompile 0x01 | ECDSA recovery, binds result address | `evm_ecrecover_precompile` |
| `Precompiles.sha256Memory` / `Precompiles.sha256` | Precompile 0x02 | SHA-256 over an existing memory slice, binds digest word | `evm_sha256_precompile` |
| `Precompiles.bn256Add` | Precompile 0x06 (EIP-196) | BN254 (alt_bn128) point addition; binds two output coordinate words and reverts on precompile failure | `evm_bn256_add_precompile` |
| `Precompiles.bn256ScalarMul` | Precompile 0x07 (EIP-196) | BN254 scalar multiplication; binds two output coordinate words and reverts on precompile failure | `evm_bn256_scalar_mul_precompile` |
| `Precompiles.bn256Pairing` | Precompile 0x08 (EIP-197) | BN254 optimal-Ate pairing check over a caller-supplied input region; binds the single 32-byte boolean word | `evm_bn256_pairing_precompile` |
| `Callbacks.callback` | Parameterized | ABI-encode selector + static args + bytes, call target | `callback_target_interface` |
| `Calls.withReturn` | Parameterized | Generic call/staticcall with single uint256 return | `external_call_abi_interface` |
| `Oracle.typedReadWordSummary` | Typed-interface `view` read | ABI-encode selector + static args, `staticcall` target, bind one static ABI-word return, and surface the source-shaped summary name and selector | `oracle_summary:<Interface.method>` (`oracle_summary:{summaryName}` in the module template) |
| `Oracle.oracleReadUint256` | Legacy generic oracle read | ABI-encode selector + static args, `staticcall` target, bind one uint256 return | `oracle_read_uint256_interface` |
| `Calls.callWithValue` | Parameterized | Generic `call{value:v}` over an already prepared calldata slice, with revert bubbling | `generic_call_with_value_interface` |
| `Calls.callWithValueBytes` | Parameterized | Generic `call{value:v}` over a `bytes` parameter, with revert bubbling | `generic_call_with_value_interface` |
| `Calls.bubblingValueCall` / `Calls.bubblingValueCallNoOutput` | `call{value: v}(data)` shape | Generic low-level value call over caller-provided memory slices; bubbles exact revert returndata on failure | `generic_low_level_value_call_interface` |
| `Create2SSTORE2.create2Deploy` | Parameterized | `create2(value, offset, size, salt)` over caller-prepared initcode | `create2_initcode_layout`, `create2_address_derivation` |
| `Create2SSTORE2.sstore2ReadCode` | Parameterized | `extcodecopy(pointer, dest, codeOffset, size)` for code-as-data reads | `sstore2_pointer_code_layout` |

See `Compiler/Modules/README.md` for the full checklist on adding new standard modules.

### Generic `callWithValue` Adapters

`Calls.callWithValue target value inOffset inSize` is the low-level adapter
escape hatch for patterns such as arbitrary DeFi routers: the caller prepares
calldata in memory, the ECM emits `call(gas(), target, value, inOffset, inSize,
0, 0)`, and failures bubble returndata. Successful returndata is intentionally
ignored; wrappers that need typed return decoding should build a narrower ECM.
`Calls.callWithValueBytes target value "data"` is the higher-level
`(target, value, data)` wrapper: it copies the named `Bytes` parameter payload
to memory offset 0 and then emits `call(gas(), target, value, 0, data_length,
0, 0)`. Trust reports surface raw slice calls as `callWithValue` and bytes
wrapper calls as `callWithValueBytes` so audit manifests can distinguish which
adapter surface a contract used.

### Generic Value Calls

`Compiler.Modules.Calls.bubblingValueCall` is the standard Verity-core surface
for Solidity-style arbitrary low-level calls:

```lean
Compiler.Modules.Calls.bubblingValueCall
  (Expr.param "target")
  (Expr.param "ethValue")
  (Expr.param "inputOffset")
  (Expr.param "inputSize")
  (Expr.param "outputOffset")
  (Expr.param "outputSize")
```

It lowers to `call(gas(), target, ethValue, inputOffset, inputSize,
outputOffset, outputSize)`. On failure, it copies `returndatasize()` bytes from
offset zero into memory offset zero and reverts with that exact payload. The
module is marked state-writing and state-reading, so normal mutability and CEI
checks still apply; in particular, it is rejected from `view` / `pure`
entrypoints rather than being treated as a read-only interface.

This module models only generic EVM call mechanics. The meaning of the calldata,
the callee's behavior, and protocol-specific postconditions remain assumptions
of the package that uses the call.

For adapter/router calls that intentionally ignore successful returndata, use
`Compiler.Modules.Calls.bubblingValueCallNoOutput target value inputOffset
inputSize`. It is backed by the four-argument
`bubblingValueCallNoOutputModule`, which is suitable for `verity_contract`
`ecmDo` call sites. Trust reports surface the distinct
`bubblingValueCallNoOutput` module name with the same
`generic_low_level_value_call_interface` assumption.

### ERC-20 Optional Return Policies

`Compiler.Modules.ERC20.safeTransfer`, `safeTransferFrom`, and `safeApprove`
use an OpenZeppelin-style optional-return policy: a successful call is accepted
only if it returns exactly one ABI bool word equal to `true`, or if it returns no
data and the token address has code. Malformed short or oversized returndata,
`false`, and no-return EOAs revert with `SafeERC20FailedOperation(address)`.

`Compiler.Modules.ERC20.solmateSafeTransfer` and
`solmateSafeTransferFrom` are provided for contracts that need Solmate
`SafeTransferLib` parity. They accept successful empty returndata without an
`extcodesize` check, and accept non-empty returndata when
`returndatasize() > 31` and the first returned word is `true`. Failed calls
bubble returndata before the optional-return guard runs.

`Compiler.Modules.ERC20.legacyStringSafeTransfer` and
`legacyStringSafeTransferFrom` implement the "legacy string error" style used by
Morpho Blue's `SafeTransferLib` (and some other older custom SafeTransferLib
libraries). They always perform an `extcodesize` check (reverting with the classic
`Error("no code")` string), and on failure or bad optional bool they revert with
specific `Error("transfer reverted")` / `Error("transfer returned false")` etc.
strings (using the classic `Error(string)` encoding). Inner returndata is not
bubbled on call failure. This produces byte-compatible observable behavior with
contracts that chose this particular SafeTransferLib flavor.

These reusable helpers can be used with typed-interface token parameters; the
interface parameter still lowers as an address, while the helper selects the
appropriate Safe* ECM instead of the ordinary typed-interface `transfer` call:

```lean
interfaces
  interface IERC20 where
    function transfer(Address, Uint256) returns (Bool)
  end

function pushTokens (token : IERC20, to : Address, amount : Uint256) : Unit := do
  safeTransfer token to amount
```

For the legacy string style used by Morpho, use the explicit legacy helpers:

```lean
function pushTokensLegacy (token : IERC20, to : Address, amount : Uint256) : Unit := do
  legacyStringSafeTransfer token to amount
```

Use the direct helper form when a token boundary needs optional-return
semantics. A dot call such as `let ok ← token.transfer to amount` remains the
ordinary typed-interface call path and requires exactly one returned word.

The choice of helper determines the exact revert data and guard semantics. This
keeps the three common real-world SafeTransferLib styles (OZ, Solmate, legacy
string) first-class and explicitly named, rather than hidden behind a generic
"policy" parameter.

### Callback Helpers

`Compiler.Modules.Callbacks.callback` builds callback calldata at the Solidity
free-memory pointer, advances the pointer by the padded ABI frame, performs a
plain `call`, and bubbles exact revert returndata on failure. The helper fixes
the selector/static-argument/dynamic-bytes ABI layout, while the callback
target's protocol-specific behavior remains the `callback_target_interface`
assumption.

### CREATE2 and SSTORE2 Helpers

`Compiler.Modules.Create2SSTORE2.deployModule` lowers a source-level ECM call to
`create2(value, offset, size, salt)` and binds the returned address word. The
caller is responsible for preparing the initcode memory slice and for proving or
assuming the `create2_initcode_layout` and `create2_address_derivation`
boundaries.

`Compiler.Modules.Create2SSTORE2.readCodeModule` lowers to `extcodecopy` for
SSTORE2-style code-as-data reads. The helper only models the copy mechanic; the
meaning of the pointer's bytecode layout remains the
`sstore2_pointer_code_layout` assumption.

### Typed CodeData Facade (#1967)

`Compiler.Modules.CodeData` is the typed source-level facade over the
CREATE2 / SSTORE2 helpers above. It pairs each write/read site with a
`Compiler.ABI.Frame.FrameLayout` so the payload shape is statically
typed, materialises the payload into memory via `Frame.materializePayloadToMemory`,
and routes through the underlying ECMs:

- `Compiler.Modules.CodeData.writeTyped resultVar base write` — typed
  write. The `write : CodeDataWrite` carries a `FrameLayout` payload, an
  optional ETH value, and a salt. Fails closed if the layout contains
  any dynamic field (`Frame.layoutSourcesSupported` is the gate); this
  is intentional because SSTORE2-style code-as-data is only sound for
  static layouts.
- `Compiler.Modules.CodeData.readTyped read` — typed read. Lowers to the
  underlying `extcodecopy` ECM after a matching layout-sources check.
- `Compiler.Modules.CodeData.roundtripShape resultVar base write read` —
  combined write+read, useful for tests and Midnight-style
  `toId`/`toMarket`/`touchMarket` round-trip patterns.

Coverage in `Compiler.Modules.CodeDataTest` exercises the typed surface
on (a) the full multi-field blob+meta payload, (b) an empty payload (no
fields), (c) a one-word short payload, and (d) a dynamic payload — the
last must be rejected with an explicit error so callers never silently
store ABI-encoded dynamic tails into pointer code.

### Packed Hashing Helpers

`Compiler.Modules.Hashing.abiEncodeStaticWords` covers
`keccak256(abi.encode(...))` when every argument is already represented as a
complete 32-byte ABI word. This is the common static preimage shape for
`uint256` / `bytes32` hashes and EIP-712 struct hashes after the caller has
constructed any nested field hashes. Dynamic values, nested dynamic tails, and
sub-word normalization remain explicit caller responsibilities or should use a
more specific helper.

`Compiler.Modules.Hashing.abiEncodePackedWords` and
`Compiler.Modules.Hashing.sha256PackedWords` cover the audit-critical static
word subset of packed preimage construction. The shorter
`Compiler.Modules.Hashing.abiEncodePacked` and
`Compiler.Modules.Hashing.sha256Packed` aliases expose the same semantics. They
are intended for values that already occupy complete ABI words, such as
`uint256`, `bytes32`, and address values after the model has chosen its
word-level representation.

The current helpers deliberately do not claim full Solidity
`abi.encodePacked` parity for dynamic bytes/strings. For static mixed-width
preimages, `Compiler.Modules.Hashing.abiEncodePackedStaticSegments` and
`Compiler.Modules.Hashing.sha256PackedStaticSegments` accept explicit byte
widths from 1 to 32:

```lean
Compiler.Modules.Hashing.abiEncodePackedStaticSegments
  "digest"
  [(Expr.param "who", 20), (Expr.param "amount", 32)]
```

Sub-word segments are masked to their requested width and left-aligned before
`mstore`, then subsequent segments are placed at byte-precise offsets so later
writes overwrite the unused tail bytes from earlier sub-word stores. These
segment helpers expose
`abi_packed_static_segment_layout` separately from the word-only layout
assumption. Dynamic packed inputs should still be spelled out explicitly or
added through a focused helper with its own tests and trust-report assumption.

For EIP-712 typed-data digests, use `Compiler.Modules.Hashing.eip712Digest`.
It fixes the standard `keccak256(abi.encodePacked(hex"1901",
domainSeparator, structHash))` preimage layout at 66 bytes. Domain separator
and struct-hash construction remain explicit model code, and `ecrecover`
cryptographic correctness remains the EVM precompile assumption surfaced by
`Compiler.Modules.Precompiles.ecrecover`.

## Writing Your Own ECM

### Minimal Example

```lean
import Compiler.ECM
import Compiler.CompilationModel

namespace MyProtocol

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr)

def myCallModule : ExternalCallModule where
  name := "myCall"
  numArgs := 2  -- token, amount
  writesState := true
  readsState := false
  axioms := ["my_protocol_interface"]
  proofStatus := .assumed
  compile := fun _ctx args => do
    let [token, amount] := args | throw "myCall expects 2 arguments"
    -- Your Yul generation logic here
    pure [YulStmt.expr (YulExpr.call "call" [
      YulExpr.call "gas" [], token, YulExpr.lit 0,
      YulExpr.lit 0, YulExpr.lit 0, YulExpr.lit 0, YulExpr.lit 0
    ])]

def myCall (token amount : Expr) : Stmt :=
  .ecm myCallModule [token, amount]
```

### CompilationContext

The `compile` function receives a `CompilationContext` with:

- `isDynamicFromCalldata : Bool`, whether dynamic data (bytes, arrays) comes
  from calldata (external functions) or memory (internal functions). Use this
  to emit `calldatacopy` vs `mcopy` as appropriate.

### Validation

Module-specific validation (selector bounds, parameter name checks, etc.)
should be performed in the `compile` function, which returns `Except String`.
The generic `Stmt.ecm` path handles:

- Argument count validation
- View/pure mutability enforcement via `writesState`/`readsState`
- Result variable shadowing and redeclaration checks

### Testing

Add compile-time tests in `Compiler/CompilationModelFeatureTest.lean` using
`#eval! do` blocks. At minimum, test:

1. Successful compilation (smoke test)
2. Mutability rejection (if `writesState = true`, test view rejection)
3. Any module-specific validation (e.g., selector overflow)

## Third-Party Modules

Protocol-specific modules should live in external Lean packages:

```
my-verity-ecm/
├── MyProtocol/
│   ├── Swap.lean
│   └── Oracle.lean
├── AXIOMS.md        -- Document all trust assumptions
└── lakefile.lean    -- depends on verity (specifically Compiler.ECM)
```

In `lakefile.lean`:
```lean
require verity from git "https://github.com/lfglabs-dev/verity.git" @ "main"
```

Import path: `import MyProtocol.Swap`.

## Axiom Aggregation

Every ECM declares its trust assumptions in the `axioms` field and tags the
surface with `proofStatus`. When compiling with `--verbose`, the compiler
aggregates both the assumptions and the status buckets, emitting a
localized `Usage-site trust report` section before the contract-level reports:

```
ECM axiom report:
  MorphoBlue:
    [safeTransfer] erc20_transfer_interface
    [safeTransferFrom] erc20_transferFrom_interface
    [callback] callback_target_interface
    [ecrecover] evm_ecrecover_precompile
```

Each assumption is tagged `proved`, `assumed`, or `unchecked`, localized to the
constructor or function that introduced it, and classified with a
machine-readable `boundaryClass`. Current classes include `compilerIntrinsic`,
`abiBoundary`, `externalCall`, `oracleSummary`, `tokenModel`, `callback`,
`event`, `gate`, and `storageLayoutAssumption`.

For a machine-readable version, run `verity-compiler --trust-report <path>`. The JSON covers ECM assumptions, linked externals, axiomatized primitives, low-level mechanics, proof-gap categories, boundary classes, and a `hasUncheckedDependencies` flag for CI gating. Use `--assumption-report <path>` when audit tooling needs a flat inventory of every localized obligation. See [VERIFICATION_STATUS.md](./VERIFICATION_STATUS.md#solidity-interop-support-matrix-issue-586) for the full trust-report schema.

To discharge an obligation, replace the relevant linked external / ECM / local
obligation status with a proved surface and keep its axiom name stable so audit
manifests can track the proof. To intentionally assume a boundary, keep the
status as `assumed`, document the assumption beside the module or contract, and
archive the trust or assumption report. For proof-strict runs, use the
fail-closed flags below so any remaining assumed or unchecked boundary aborts
compilation with the exact usage site.

**Fail-closed flags**: a set of `--deny-*` flags lets you reject specific trust surfaces at compile time. Each flag fails the build and reports the exact usage site. See the [full flag table in VERIFICATION_STATUS.md](./VERIFICATION_STATUS.md#solidity-interop-support-matrix-issue-586) for the complete list. The most relevant for ECM users:

| Flag | Rejects |
|------|---------|
| `--deny-unchecked-dependencies` | Any `unchecked` linked external or ECM module |
| `--deny-assumed-dependencies` | Any `assumed` or `unchecked` linked external or ECM module |

## Trust Model

- The compiler trusts that `mod.compile` produces Yul that correctly implements
  the pattern described by the module's name, documentation, and axioms.
- This trust is scoped: a bug in one module does not affect contracts that don't
  use it.
- Standard modules in `Compiler/Modules/` are maintained and audited alongside
  the compiler.
- Third-party modules are outside the Verity team's trust boundary.
- Verity core owns generic Solidity/EVM mechanics such as low-level call
  lowering, returndata bubbling, mutability flags, CEI tracking, and trust
  reporting. Protocol-specific assumptions, including Unlink's Permit2,
  Poseidon, Lazy-IMT, and Groth16 verifier boundaries, should live in the
  dependent package as linked externals or package-local ECMs.

See `TRUST_ASSUMPTIONS.md` section 7 and `AXIOMS.md` for details.
