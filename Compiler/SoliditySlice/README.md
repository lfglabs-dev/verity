# Solidity function slices

`solidity_slice_import` elaborates a selected Solidity function and its reached
helpers into the ordinary Verity `CompilationModel`. It consumes a checksum-pinned
solc 0.8.34 AST and storage layout. There is no separate slice interpreter.

```lean
import Compiler.SoliditySlice.Import

solidity_slice_import example
  slice_root "Contracts/SoliditySliceSmoke" slice_entry "Slice.sol"
  slice_contract "C" slice_function "f"
  slice_param_tys ["struct Mkt", "bytes32", "address"]
  slice_solc "0.8.34+commit.80d5c536" slice_via_ir true slice_evm "osaka"
  slice_optimizer true slice_runs 466 slice_bytecode_hash "none"
```

The command defines `example.model`, `example.report`, `example.sourceDigest`,
and the kernel theorem `example.sliceCovered`. It also works inside namespaces.
`example.report.toText` renders the included/excluded signatures, projections,
opaque members, settings, and source digest.

Install the compiler with `python3 scripts/setup_solc_slice.py`; a downstream
package can pass `--output .lake/solidity-import/solc-0.8.34`. Elaboration never
downloads a compiler. `slice_root` resolves relative to the importing package's
`lakefile.lean`, and imports use the project's `remappings.txt`.

## Supported boundary

This is deliberately the subset needed by Midnight's `updatePositionView`,
not a claim to support arbitrary Solidity.

| Construct | Lowering |
| --- | --- |
| Explicit scalar/tuple return | `returnValues`, preserving order |
| Local declarations and storage aliases | Hygienic scalar bindings or resolved read paths |
| One/two-key mappings to structs | solc slots, word offsets, and packed uint offsets |
| Read scalar member of a memory/calldata struct parameter | Explicit scalar projection; no public ABI decoder |
| Unsigned `+`, `-`, `*`, `/` | Word arithmetic with overflow/underflow/zero-divisor guards |
| Unsigned comparisons, equality | Scalar conditions |
| Narrowing casts | Bit masks, not overflow checks |
| Ternaries | Lazy `ite` branches |
| Resolved acyclic helper calls | Inlined bodies with separate local scopes |
| Single assignment to a named assembly return | `xor`, `mul`, `lt` expressions, as in `UtilsLib.min` |

The root must return explicitly. Loops, state writes, external calls, modifiers,
recursion, virtual dispatch, named call arguments, signed operations, and
unrecognized reached constructs are rejected. Unsupported functions outside the
closure are recorded as excluded. Only reached storage fields are decoded;
opaque array/mapping members are reported and cannot be read. Scalar projections
are checked for parameter-name collisions.

## Determinism and trust

Function selection uses the contract, name, and full parameter-type list. Helper
resolution uses solc declaration IDs. Generated names cannot capture Solidity
identifiers; helper-local environments are restored after inlining. Field and
function ordering is deterministic. The digest uses framed JSON containing the
complete solc input, selected signature, release identity, and importer sources.
The report records the checksum actually verified for the invoked compiler.

A covered constructor has an explicit denotation arm. Coverage is **not** a
proof of source-to-model fidelity, nor membership in the compiler's proven IR
fragment. The translator and solc remain trusted; public ABI decoding, panic
payloads, gas, and bytecode equivalence are outside this interface.

Lake does not track Solidity files read during elaboration. Consumers must
re-elaborate the import when checking external source freshness, compare the
fresh model/digest with the compiled import, and retain a reviewed inventory.
The Morpho pilot demonstrates that workflow along with universal properties on
`Denote.execStmtList`, rather than properties only on handwritten arithmetic.

## Validation

```sh
lake build SoliditySliceSmoke
python3 scripts/solidity_slice_mutations.py
```

The regression suite exercises helper/local-name hygiene, namespace use,
shadowed builtins, narrow multiplication overflow, repeated deterministic imports,
unrelated unsupported storage, explicit rejection
of named arguments and implicit returns, reached/unreached unsupported loops,
and detection of changes to arithmetic, field reads, layout, and return order.
The smoke interpreter checks do not replace kernel proofs.
