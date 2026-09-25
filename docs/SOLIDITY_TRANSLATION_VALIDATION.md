# Translation validation feasibility: `UtilsLib.mulDivDown`

Status: **the actual imported wrapper and captured native arithmetic body have
kernel-checked successful return-byte equivalence; whole-dispatcher and
failure-inclusive translation equivalence is not implemented**.
This experiment does not change the importer, its acceptance criteria, the trust
boundary, or any existing theorem. In particular, it does not remove the Solidity
frontend from the trusted computing base.

## Pinned experiment

The source is `src/libraries/UtilsLib.sol` from
`morpho-org/midnight@96d31343e993329e7a593dde46516a2c0cbcd142`, Git blob
`da30b5f2ae048eabdab031d6b4fac9caee442e0b`. The full file is embedded unchanged in
the standard JSON input. A separate external wrapper calls the original internal
function, since compiling the library alone does not expose the internal helper
as an executable entry point. The source implementation is checked arithmetic:
`return (x * y) / d;`. It is not a 512-bit multiply/divide routine.

[`capture.py`](../experiments/solidity-translation-validation/capture.py) verifies
the source blob, compiler binary SHA-256 and compiler banner before compilation.
It uses the importer's solc `0.8.34+commit.80d5c536`, `viaIR: true`, optimizer runs
466, EVM Osaka, and `bytecodeHash: none`. Standard JSON `irOptimized` is the output
corresponding to CLI `--ir-optimized`; `irOptimizedAst` is captured alongside it.
The settings and complete inputs are in
[`input.json`](../experiments/solidity-translation-validation/input.json), actual
compiler output in
[`MulDivDown.optimized.yul`](../experiments/solidity-translation-validation/MulDivDown.optimized.yul),
and content hashes in
[`manifest.json`](../experiments/solidity-translation-validation/manifest.json).
The AST is compiler output, not a hand-written translation.

The **initial source survey** examined Verity
`9934dd6cefb84cf3a51dc598fa7a89f3cae8e21b`. The first executable proof/check
runs used `f809b27dcde780e3a8420563d27aa09c28c0fdd3`; their environment is
preserved in
[`proof-environment.f809b27d.json`](../experiments/solidity-translation-validation/proof-environment.f809b27d.json).

The **current integration checks** use
`/Users/thomas/work/verity-translation-validation` at
`11cfc7a87761d3c964dbedba6b88ca356d26d30d`, verified with `git rev-parse HEAD`.
The prototype sources are untracked additions; tracked source files are
unchanged. The integration branch was fast-forwarded from `a742733d` to this
merged main revision before checking. These survey and executable revisions
are different and must not be conflated. The current manifest and dependency
checkout both pin EVMYulLean at
`f7e4ee0dc8f8d5265ce822a937ab5be771f182e9`. No Solidity source, compiler,
EVMYulLean or pilot pin changed.

[`proof-environment.json`](../experiments/solidity-translation-validation/proof-environment.json)
records the current executable head, Lean banner/toolchain, manifest hash,
actual dependency heads, prototype source hashes and focused check commands.
The integration worktree received a **private APFS clone** of the frozen
`verity-stateful-sequences/.lake` cache/packages, with distinct file inodes,
then ran the normal `lake build` for every imported project prerequisite before
the prototype checkers. No donor files were modified and no cache symlinks were
introduced. This is an incremental dependency build, not a clean build of the
entire project. Before publishing against another head, rebuild prerequisites
and rerun every focused checker there; this receipt does not cover a newer head.

## What the optimized program requires

The runtime dispatcher decodes selector `0xb67bee04` and three 256-bit arguments.
Its relevant arithmetic is exactly:

```yul
let product := mul(value, value_1)
if iszero(or(iszero(value), eq(value_1, div(product, value)))) {
    mstore(0, shl(224, 0x4e487b71))
    mstore(4, 0x11)
    revert(0, 36)
}
if iszero(value_2) {
    mstore(0, shl(224, 0x4e487b71))
    mstore(4, 0x12)
    revert(0, 36)
}
mstore(_1, div(product, value_2))
return(_1, 32)
```

For canonical decoded inputs `x,y,d < 2^256`, the required specification is:

* If `x*y >= 2^256`, revert with the 36 bytes encoding `Panic(0x11)`.
* Otherwise, if `d = 0`, revert with the 36 bytes encoding `Panic(0x12)`.
* Otherwise, return the 32-byte unsigned encoding of `x*y / d`.

Overflow takes precedence when both failures apply. In particular, `(0,y,0)`
must report division by zero, while `(2^256-1,2,0)` must report overflow. Storage
and logs stay unchanged; intermediate memory is private execution state, while
the bytes selected by return/revert are observable. Whole-entry validation must
also account for nonzero call value, malformed calldata and unknown selectors.
ABI-valid calldata need not have exactly 100 bytes: the captured dispatcher
accepts trailing bytes.

`Import.lean` already lowers checked multiplication using the zero-left-operand
case followed by a division-based overflow check, then lowers checked division
with a separate zero-denominator panic. This is promising structural alignment,
but inspection is not an equivalence proof.

## Kernel-checked intermediate prototype

[`Arithmetic.lean`](../experiments/solidity-translation-validation/Arithmetic.lean)
proves six universal lemmas:

* `mul_overflow_guard_iff`: for every positive modulus and natural `x,y`, the
  zero-aware modular division guard holds exactly when `x*y < modulus`.
* `denote_word_mul_overflow_guard_iff`: specializes that result to the actual
  `Uint256` multiplication/division operations used by Denote, on canonical
  256-bit inputs.
* `native_mul_overflow_guard_iff`: establishes the corresponding predicate using
  EVMYulLean's actual native division builtin bridge.
* `native_product`: connects the guard's product to EVMYulLean's actual modular
  multiplication builtin bridge.
* `native_mul_div_success`: native multiply then divide returns `x*y/d` when the
  product fits and the canonical denominator is nonzero.
* `denote_mul_div_success`: Denote's word operations yield the same quotient
  under canonical input bounds, no overflow, and a nonzero denominator.

These use `EvmYulLeanPureBuiltinLemmas`; the small word-division argument follows
the existing `SolidityImport.Proofs.div_word` reasoning. They introduce no
replacement `CompilationModel`, no new arithmetic oracle, and no imported-model
or dispatcher execution claim. The `#print axioms` receipts contain only
`propext`, `Quot.sound`, and, for the native guard theorem, `Classical.choice`.
There are no project axioms or proof escapes.

[`check_arithmetic.py`](../experiments/solidity-translation-validation/check_arithmetic.py)
checks all six proofs, checks their axiom receipts, and verifies rejection of
three altered statements: removing the zero-product case, changing the modulus,
and substituting native division for native multiplication. These test the
intermediate arithmetic statements; they are not importer mutation coverage or
a certificate binding the Lean lemmas to the captured solc AST.

[`Imported.lean`](../experiments/solidity-translation-validation/Imported.lean)
now runs **actual `solidity_import`** over the original full `UtilsLib.sol` and
wrapper materialized under the experiment's `sources/` directory. These files
come directly from the already-captured standard JSON input; no source body is
rewritten. `capture.py --check` includes these materialized files, and the proof
runner independently checks the library's pinned Git blob and exact wrapper.

`captured_success` universally proves, for any oracle and initial world and
canonical `Uint256` inputs with `x.val*y.val < 2^256` and `d.val ≠ 0`:

```lean
captured.mulDivDown oracle world x y d =
  some (Uint256.ofNat (x.val * y.val / d.val))
```

The proof unfolds the generated model's actual `runFunction`/`execStmtList`
execution, including its overflow branch and zero-denominator branch, and uses
the arithmetic lemmas above to establish successful execution. There is no
hand-written substitute model or assumed model-equality premise.

`captured_success_matches_native_arithmetic` then equates that successful
wrapper result, projected to its word value, with EVMYulLean's actual native
`mul` followed by `div`. This relates the imported function to native arithmetic
composition, **not** the complete captured optimized AST. It does not prove
ABI decoding, exact output bytes, rollback, panic payloads, or Yul dispatcher
execution. Both new theorems use only `propext`, `Classical.choice`, `Quot.sound`.

Historical receipts from the first successful proof run at `f809b27d`:

* `captured.sourceDigest`:
  `b4abb578de931278887aeddde6712a69c1c9440f717b63119641bb00f30867ad`.
  This importer digest includes compiler settings, source inputs and importer
  source text; future importer edits can legitimately change it and require a
  fresh proof run.
* Original `UtilsLib.sol` SHA-256:
  `0c33e0537fc1bfca2f43c2a7440bbc919202b5f6548310252f35843cc11afb14`.
* Wrapper SHA-256:
  `f9d15bfa7f658b89d705166a087fada0feb297030930855ffbadc346621c3c55`.
* Captured optimized Yul SHA-256 (unchanged):
  `42533dc6d3b36a3aac988012250647bf21fa1be3908e0b104524cd6636913851`.

The full eight-theorem check is `python3
experiments/solidity-translation-validation/check_arithmetic.py`. It first
builds the small arithmetic module into the local Lean cache, checks its three
incorrect variants, then elaborates the actual Solidity import and checks both
success theorem axiom receipts.

## Actual optimized-AST binding and native execution

The optimized output contains no surviving `mulDivDown` Yul function: solc
inlines its body into the dispatcher. The prototype selects the actual five
contiguous arithmetic-body statements: product declaration, overflow guard,
denominator guard, return-word store, and return. It does not invent a replacement
Yul function or identify an arbitrary
hand-written term with compiler output.

[`generate_ast_bridge.py`](../experiments/solidity-translation-validation/generate_ast_bridge.py)
requires the exact pinned optimized JSON and Yul hashes. It follows recorded JSON
paths and emits complete `Lean.Json` constructor quotations of the selected
nodes, including their source metadata, plus native AST terms. The generated
[`CapturedNodes.lean`](../experiments/solidity-translation-validation/CapturedNodes.lean)
records the paths and the corresponding optimized-Yul byte spans:

* product expression: `nativeSrc = 1183:19:0`, `mul(value, value_1)`;
* quotient expression: `nativeSrc = 1764:21:0`, `div(product, value_2)`;
* product declaration: body statement 5, `nativeSrc = 1168:34:0`.

The generated `CapturedNodes.lean` is reproducibly checked by the generator;
its SHA-256 for the five-statement body capture is
`cd1adc0f9b7aa06245959dcf8891860688a7610920dea14d9d7b670374893b6a`.
The original optimized JSON retains SHA-256
`60059226825f5eea534dad2f8a705fa81bd1924011a308f428181dc694d9f92c`.

[`AstDecoder.lean`](../experiments/solidity-translation-validation/AstDecoder.lean)
is a pure, fuel-bounded Lean decoder. It accepts identifiers, bounded number
literals, the exact unsigned arithmetic/boolean/shift builtins used here, single
initialized declarations, `if` statements, and the `mstore`, `revert`, `return`
statement calls. Void calls cannot occur in pure expression positions. Decimal
and hexadecimal literals are checked digit by digit and must fit one word.
It rejects unknown
node kinds, builtin names, arities, declaration types, additional semantic
fields, and exhausted decoding fuel. It does not treat signed division or
unimplemented nodes as unsigned arithmetic. The generated `decodeProduct`,
`decodeQuotient`, `decodeProductDeclaration`, `decodeOverflowGuard`,
`decodeDenominatorGuard`, `decodeReturnStore`, and `decodeReturn` equations are
proved by kernel reduction (`rfl`), so every selected native AST statement is
checked against its quoted JSON. Both original panic bodies remain intact.

[`CapturedExecution.lean`](../experiments/solidity-translation-validation/CapturedExecution.lean)
then proves **actual `EvmYul.Yul.eval` and `exec` results**, using the pinned
interpreter and its existing primitive-operation lemmas:

* `decoded_product_executes` and `decoded_quotient_executes` pair those decoder
  equations with universal execution theorems at fuel 10. They return the
  corresponding native word operation and preserve the complete input state.
* `exec_captured_product_declaration` executes the selected real declaration and
  establishes its exact local insertion, leaving shared state untouched.
* `captured_quotient_success` proves the mathematical quotient at the selected
  return-store expression under explicit `product` and denominator bindings,
  a fitting product, a canonical nonzero denominator, arbitrary native state,
  and arbitrary code override.

The last expression theorem's binding hypotheses are **not** a proof that
dispatcher execution establishes those bindings. The newer
[`GuardedExecution.lean`](../experiments/solidity-translation-validation/GuardedExecution.lean)
does establish the body data flow and composes all five actual statements:

* `overflow_guard_passes` proves the real solc predicate evaluates to zero under
  the product-fit bound, treating `x=0` separately. It does not assume the guard
  result. `denominator_guard_passes` similarly derives the zero predicate from a
  nonzero canonical denominator.
* `captured_guarded_prefix_continuation` composes the product insertion with
  both guards and reaches any following statement list with the correct product
  local. Shared state remains unchanged across that prefix.
* `captured_arithmetic_body_success` executes the real five-statement body slice
  at fuel 100, through `mstore` and `RETURN`. Its result is precisely:

```lean
Yul.exec 100 capturedArithmeticBody code (.Ok shared store) =
  .error (.YulHalt (successfulBodyState shared store x y d) (UInt256.ofNat 1))
```

`YulHalt` is the native interpreter's **successful RETURN** constructor, distinct
from `Revert`. The final-state definition uses the actual native machine-state
operations `mstore(128, x*y/d)` followed by `evmReturn(128,32)`, preserves the
original shared contract state, and adds the product local to the original
variable store. It does not replace memory by a word-list approximation.

The theorem quantifies over arbitrary native shared state, variable store and
code override, with explicit decoded `value`, `value_1`, `value_2` bindings,
canonical input bounds, `x*y < 2^256`, `d ≠ 0`, and `_1 = 128`. The last premise
is the buffer pointer established by solc's `memoryguard(0x80)` prologue; that
prologue and ABI/selector decoding are not executed by this theorem.

[`ReturnObservation.lean`](../experiments/solidity-translation-validation/ReturnObservation.lean)
now normalizes that native byte-memory result and composes it with the imported
wrapper. `write128_return32` proves that writing a full 32-byte source at offset
128 and reading those 32 bytes returns the original source, for **arbitrary
initial memory**, including buffers shorter or longer than the output range.
`successfulBodyState_bytes` instantiates this with the quotient word's native
big-endian `UInt256.toByteArray` encoding. No empty-memory premise is added.

The composed theorem `captured_body_bytes_match_imported` states:

```lean
nativeReturnBytes (Yul.exec 100 capturedArithmeticBody code (.Ok shared store)) =
  (captured.mulDivDown oracle world x y d).map
    (fun word => (UInt256.ofNat word.val).toByteArray)
```

It quantifies over every Denote oracle/world and native shared state/store/code,
with the same canonical words, fitting product, nonzero denominator, decoded
input bindings and `_1 = 128` premises as the body-success proof. The observation
selects only native `YulHalt` with success status 1. The previously proved exact
execution equation also remains available; the new observation equality does
not hide a revert as success. This encodes the actual imported return word,
without substituting a hand-written model or assuming either side's result.
It does not establish Verity-compiled bytecode equivalence, the dispatcher/ABI
premises, or failure-byte equivalence. Failure paths remain subject to the
revert-payload obstruction below. Whole-function equivalence is still not claimed.

The artifact-to-`Lean.Json` quotation uses Python JSON parsing and source
selection. That small generation boundary is pinned, reproducibly checked and
tested, but is not itself kernel-proved equivalent to parsing the original byte
file. The Lean decoder equations certify the quoted JSON-to-native-AST step;
they must not be presented as eliminating every frontend trust assumption.

`python3 experiments/solidity-translation-validation/check_ast_bridge.py` checks
regeneration, builds only the small decoder/node modules into the existing Lean
cache, and checks native execution proofs and their axiom receipts. It also
kernel-checks 20 precise decoder rejection cases, including all original nine,
invalid/oversized/empty literals, unary-arity errors, void calls in expressions,
statement fuel, and unsupported/incorrectly applied effects. It rejects proof
mutations changing the overflow disjunction and the returned quotient, and
verifies that corruption of either optimized artifact fails before quotation.
All proof receipts contain only the standard Lean axioms.

## Integration receipt at `11cfc7a8`

The full proof campaign passes on the merged integration base without changing
any Lean proof or accepted/rejected test. The actual imported wrapper now prints:

```text
captured.sourceDigest = 986f54041a50df2ea661226062684d883a176635138a2bdd6331e08329e19a23
```

The historical digest was
`b4abb578de931278887aeddde6712a69c1c9440f717b63119641bb00f30867ad`.
This is an expected provenance change: `Import.lean` hashes the importer source
texts as well as the solc input and selected function. Since `f809b27d`, the
hashed `Import.lean`, `Coverage.lean` and `Report.lean` changed to preserve/report
Denote panic payloads and precisely reject declarations without initializers.
No source or generated model golden was changed to accommodate a failing test.
The captured Solidity source, wrapper, solc profile/binary and optimized Yul/AST
remain byte-identical. The unchanged success proofs now run against the rebuilt
current importer and Denote.

The normal prerequisite build exited 0 (1185 jobs):

```sh
lake build Compiler.SolidityImport.Import Compiler.SolidityImport.Access \
  Compiler.Proofs.YulGeneration.Backends.EvmYulLeanPureBuiltinLemmas \
  Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativePrimOps \
  Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness.Foundation \
  Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeCalldata
```

`check_return_observation.py` then exited 0, rerunning `check_arithmetic.py` and
`check_ast_bridge.py` before its own checks: 30 theorem receipts with only the
standard axioms, 20 precise decoder rejections, eight rejected proof mutants and
two rejected artifact corruptions. The dispatcher-boundary checker separately
passed its exact rejection receipt, native-constructor-absence probe and changed
callee mutation. Both capture and generated-quotation consistency checks also
exited 0. This validates the bounded prototype on this integration base; it is
not a whole-project or all-input translation-equivalence claim.

## Blocking issue: the captured dispatcher starts with unsupported `memoryguard`

The next attempted obligation was to derive the decoded `value`, `value_1`,
`value_2` and `_1 = 128` premises from three ABI words in real calldata. The
first runtime statement prevents an unchanged-native-semantics dispatcher proof:

```yul
let _1 := memoryguard(0x80)
```

It is the actual pinned optimized AST node at
`subObjects[0].code.block.statements[0].statements[0]`, with
`nativeSrc = 629:27:0`; the function call itself has `nativeSrc = 639:17:0`.
The whole optimized artifact hashes above remain unchanged.
[`DispatcherBoundary.lean`](../experiments/solidity-translation-validation/DispatcherBoundary.lean)
quotes this complete declaration and kernel-checks the exact rejection
`unsupported Yul builtin memoryguard`. This is an explicit boundary receipt,
not a dispatcher execution theorem.

This is also a native-semantics gap, independently of the experiment's narrow
decoder. At EVMYulLean pin
`f7e4ee0dc8f8d5265ce822a937ab5be771f182e9`,
`EvmYul/Yul/Ast.lean:37–43` represents calls as either native operations or
user-defined function names. There is no
`EvmYul.Operation.MEMORYGUARD` constructor: a focused Lean elaboration probe
rejects that exact constant. Routing it as a user-defined function would use
`Yul.call`'s ordinary function lookup (`EvmYul/Yul/Interpreter.lean:434–451`),
not supply the missing builtin semantics. The captured artifact does not define
such a function. EVMYulLean's own
`EvmYul/Yul/YulSemanticsTests/README.md:15,17` instructs its test authors to
remove `memoryguard(...)` while keeping the argument. That manual preprocessing
instruction is evidence of the gap, not a justification to perform the rewrite
inside this certificate.

`check_dispatcher_boundary.py` checks the dependency commit, both optimized
artifact hashes, and the exact quotation; builds/checks the rejection theorem;
reproduces the missing-native-constructor diagnostic; and checks that changing
the quoted callee invalidates the precise rejection theorem. Its receipt uses
only the standard Lean axioms. Existing successful-body checks are unchanged.

A future route is to extend the pinned native Yul dialect with an explicit
`memoryguard` operation and justified semantics, then prove how solc's actual
handling of that operation relates to it. An alternative is a separately
specified preprocessing transformation with a proved preservation theorem.
Neither route is implemented here; replacing this node with literal 128 now
would silently add an unproved frontend boundary. The native interpreter does
support `CALLDATALOAD`, and existing aligned-word decoding lemmas provide useful
next ingredients once the prologue boundary is resolved. This attempt does not
derive any dispatcher/ABI premise or claim whole-function equivalence. The
failure-payload issue below is independent and would remain after adding
`memoryguard`.

## Blocking issue: the native result loses revert bytes

At the pinned EVMYulLean revision, `EvmYul/Yul/Exception.lean` defines
`Exception.Revert` with **no payload or state**. More decisively,
`EvmYul/Semantics.lean:391–394` dispatches Yul `REVERT`, discards the successful
machine-state result, and returns `.error Yul.Exception.Revert`. Thus distinct
`Panic(0x11)` and `Panic(0x12)` executions cannot be distinguished from the
dispatcher result alone. This is an information-loss obstruction to the
requested exact observable theorem, not an arithmetic proof inconvenience.

Verity's current native `projectResult` in
`Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness/Projection.lean`
also maps every exception to the same failed result with rolled-back storage and
events. `YulResult` in `Compiler/Proofs/YulGeneration/RuntimeTypes.lean` carries
`Option Nat` for a return value and no revert-byte field. It cannot express the
required theorem without a richer observation type. It also identifies
interpreter failures such as out-of-fuel with contract reverts; a validator must
reject an exhausted execution instead of certifying it as an equivalent revert.

At the current integration revision, Denote's `StmtOutcome.revertWithData`
already retains explicit panic payloads. That improvement does not fix the
pinned native Yul exception above. The typed imported wrapper proved here still
uses `Access.runFunction`, which maps both Denote revert arms to `none`, so this
success-only observation does not claim failure-byte equivalence.

Fixing this requires either a payload-preserving EVMYulLean exception and its
propagation/rollback proofs, or a formally justified instrumented semantics
whose trace retains the revert payload. A projection pretending all reverts are
equal would weaken the requested property and is not an acceptable solution.
No such dependency change was made in this experiment.

## Remaining implementation and proof obligations

1. **Extend the AST bridge to the complete dispatcher.** The bounded bridge
   above certifies all five actual arithmetic-body statements and their execution.
   Extend its fail-closed decoder for `irOptimizedAst` into `EvmYul.Yul.Ast`.
   Pin/hash its input and provide tests for every accepted node and rejected
   near miss. EVMYulLean has Lean Yul
   notation, but that alone does not certify a manually copied solc program.
   Runtime-object selection, function environments, assignment representation,
   and object-only builtins require explicit treatment. This runtime contains
   `memoryguard(0x80)`; justify its executable interpretation and memory
   allocation effect rather than silently dropping it. Creation-code validation
   would additionally need `datasize`, `dataoffset` and `codecopy`.
2. **Extend the byte observations.** Successful body return bytes now agree
   with the actual imported result in `ReturnObservation.lean`. Extend both to
   panic paths with the richer observation surface.
   Preserve source/compiler digests in the certificate. Successful word-value
   agreement alone does not certify the complete observable result.
3. **Extend the guard proofs to failure paths.** The success theorem now connects
   the real guard AST and native execution to fitting arithmetic inputs. Reuse
   the universal pure builtin bridge
   lemmas in `EvmYulLeanBridgeLemmas.lean` for modular multiply, unsigned divide,
   equality, zero tests and bit operations. Establish the two panic paths,
   including their ordering and exact payloads, using the established arithmetic
   guard rather than assuming the product cannot overflow.
4. **Execute the real dispatcher symbolically.** Relate argument decoding,
   local bindings, memory writes, halt data, unchanged storage/logs, and the
   imported model's state. Use a justified sufficient fuel bound; do not assume
   away either panic path. The success-only arithmetic lemma is a useful
   intermediate result, but must be labelled as such.
5. **Specify the observation and fork.** Compare status, arbitrary return and
   revert byte strings, storage and logs. Distinguish internal interpreter errors.
   The dependency's target schedule is Cancun, while the importer smoke profile
   is Osaka. This emitted arithmetic uses older common operations, but a theorem
   must state its fork assumptions; it cannot claim general Osaka conformance.
6. **Test the validator itself.** Reject mutations to each overflow predicate,
   panic code, denominator, return length and calldata offset; reject missing or
   substituted AST artifacts. Kernel-check the resulting theorem and audit its
   axioms. Differential tests supplement this proof and do not replace it.

The final shape should universally quantify over decoded inputs and initial
worlds satisfying explicit ABI/state representation preconditions, and equate
`observe(Denote(importedModel))` to `observe(EVMYulLean(capturedRuntime))`.
Do not use an uninterpreted equality hypothesis as the main theorem's premise.
Even that theorem validates the frontend against solc's optimized Yul, **not**
solc's optimized-Yul-to-bytecode backend or the equivalence of arbitrary EVM
implementations. Those remain separate trust boundaries and differential targets.

## Receipts and next decision

On the inspected host both commands exited 0:

```sh
python3 experiments/solidity-translation-validation/capture.py \
  --midnight-repo /Users/thomas/work/morpho-midnight-verity/vendor/midnight \
  --solc /Users/thomas/work/morpho-pilot/bin/solc-0.8.34
python3 experiments/solidity-translation-validation/capture.py \
  --midnight-repo /Users/thomas/work/morpho-midnight-verity/vendor/midnight \
  --solc /Users/thomas/work/morpho-pilot/bin/solc-0.8.34 --check
```

The paths are host-local inputs, not required installation locations. `--check`
recompiles pinned sources and compares every captured artifact byte-for-byte.
The focused proof and mutation commands also exited 0:

```sh
python3 experiments/solidity-translation-validation/check_arithmetic.py
lake env lean experiments/solidity-translation-validation/Imported.lean
python3 experiments/solidity-translation-validation/check_ast_bridge.py
python3 experiments/solidity-translation-validation/check_return_observation.py
python3 experiments/solidity-translation-validation/check_dispatcher_boundary.py
```

An initial `lake build Compiler.SolidityImport.Proofs` expanded into uncached
dependencies of its broad `Mathlib.Tactic` import. That build was stopped; the
prototype instead imports cached `SolidityImport.Access` and the native builtin
lemmas. No full-project build was run for this experiment. The six arithmetic
lemmas and two actual imported-wrapper success theorems are kernel-checked;
the selected optimized-AST decoder and composed arithmetic-body execution results
are also kernel-checked. The return-observation checker first re-runs both
previous checkers, then checks three new theorem receipts and rejects three
new proof mutations: return offset 129 instead of 128, an incremented imported
return word, and success status 0 instead of 1. All three new receipts contain
only `propext`, `Classical.choice`, `Quot.sound`. Whole-Yul translation
equivalence is still not claimed.

Recommendation: keep this work below importer measurement and stateful
differential validation. Next resolve the explicit `memoryguard` semantics
boundary and establish the body's dispatcher-entry assumptions. Fix the payload-preserving native
observation boundary separately, with panic-byte and rollback regressions, before
claiming an all-input function certificate. The exact failure-inclusive theorem
remains blocked by the current native result surface.
