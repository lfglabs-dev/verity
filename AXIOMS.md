# Axioms in Verity

This file is the authoritative registry of axioms used by Verity proof code.

## Policy

Axioms are exceptional. When an axiom exists, it must have:

1. Explicit documentation in this file.
2. Source comment marking it as an axiom and linking to this file.
3. CI checks that validate usage assumptions.
4. A clear elimination path, when practical.

## Current Axioms

**None.** Verity has zero project-level Lean axioms.

- Active axioms: 0

The last remaining axiom (`solidityMappingSlot_lt_evmModulus`) was eliminated
by replacing the opaque FFI-based keccak256 call with the kernel-computable
Keccak engine (`Compiler/Keccak/Sponge.lean`), which exposes the 32-byte
output-length guarantee to Lean's proof system.

C5 step 3 (`ContractState.storageWords` over injective `StorageKey`) does
not add a keccak-injectivity axiom. Source lens laws use constructor
injectivity; Solidity slot derivation remains compiler-side.

C5 step 4's mapping-coherence, field-list, and finite-set slices
likewise add no axiom: other-pair and finite-list preservation
(address / uint / map2, including cross-channel lists) is
hypothesized by an explicit derived-slot inequality, not by keccak
injectivity. `FieldStorageKey` is a
constructor match on `FieldType` / `isTransient`; struct-member
slots add `wordOffset` via `mappingSlotLocation`. Compatibility
`aliasSlots` are extra compiler slots, not extra source keys.
bytes32-keyed maps use the same keccak preimage as uint256 keys
and do not add a `StorageKey` constructor. Mixed `address`/`uint256`
nestings likewise add no constructor. Packed extract is a shift and
mask on that word, not a new axiom.

## Eliminated Axioms

### 1. `solidityMappingSlot_lt_evmModulus` (eliminated)

**Former location**: `Compiler/Proofs/MappingSlot.lean:125`

**Former statement**:
```lean
axiom solidityMappingSlot_lt_evmModulus (baseSlot key : Nat) :
    solidityMappingSlot baseSlot key < Compiler.Constants.evmModulus
```

**How it was eliminated**:
1. `solidityMappingSlot` was redefined to use `KeccakEngine.keccak256` (kernel-computable)
   instead of `ffi.KEC` (opaque FFI).
2. `squeeze256_size` proves the output is always exactly 32 bytes.
3. `fromByteArrayBigEndian_lt_of_size` proves a ≤32-byte big-endian value is < 2^256.
4. The axiom became a theorem: `solidityMappingSlot_lt_evmModulus` is now proved,
   not assumed.

**Runtime performance**: An `@[implemented_by]` annotation optionally redirects to
the FFI version at runtime for speed, without affecting proof soundness.

## Trusted Reduction and Codegen Surface (Non-Axiom)

Verity currently has zero project-level Lean axioms, but some proofs and tests
intentionally rely on Lean mechanisms that sit outside ordinary kernel
elaboration:

- `native_decide` proofs depend on Lean's native code generation. Depending on
  the generated proof shape, `#print axioms` reports either the builtin
  `Lean.ofReduceBool` or a Lean 4.31 generated per-proof constant whose name has
  the form `…._native.native_decide.ax_<digits>`. Both forms rely on the native
  compiler trust boundary (`Lean.trustCompiler`); the generated constants are
  not Verity project axioms. They are acceptable for executable smoke tests,
  concrete bridge checks, and explicitly documented reduction witnesses, and
  are tracked as trusted reduction surface.
  Lean 4.31 exposes `String.startsWith_string_iff` and
  `String.startsWith_string_eq_false_iff`. The closed compatibility scratch-name
  facts in `Compiler/CompilationModel/ReservedScratchNames.lean` now use those
  lemmas and kernel `decide`; their former Lean 4.24 native-code trust boundary
  has been eliminated.
- `@[implemented_by ...]` may redirect runtime execution to a faster
  implementation. The proof term still sees the kernel-computable definition,
  so this is a runtime/codegen trust boundary rather than a Lean axiom.
- `partial def` marks recursive executable helpers whose termination is not
  kernel-proved. These helpers are allowed in macro, codegen, reporting, and
  native-test infrastructure, and their presence is registry-gated.

CI runs `scripts/check_trust_surface_registry.py` to ensure these mechanisms and
all explicit ECM assumptions (`axioms := [...]`) remain documented when their
source footprint changes.

### 2. Selector computation (eliminated earlier)

Function selector derivation (`bytes4(keccak256(signature))`) was previously
axiomatic. It is now kernel-computable via the vendored unrolled Keccak engine
in `Compiler/Keccak/` and `Compiler/Selectors.lean`.

### 3. Layer 2 body-simulation axiom (eliminated earlier)

The generic body-simulation axiom in Layer 2 was eliminated through explicit
proof work (issue #1618). `supported_function_correct` is now a real theorem.

### 4. Layer 3 dispatch bridge (eliminated earlier)

The dispatch bridge in Layer 3 was converted from a Lean axiom to an explicit
theorem hypothesis in `Compiler/Proofs/YulGeneration/Preservation.lean`.

## Trusted Cryptographic Primitives (Non-Axiom)

### Kernel-computable selector Keccak-256

**Location**: `Compiler/Selectors.lean`, `Compiler/Keccak/*.lean`

**Role**:
Computes function selectors (`bytes4(keccak256(signature))`) inside Lean's
kernel using a vendored unrolled Keccak-256 engine. This is now a definitional
computation, not a Lean axiom.

**Soundness controls**:
- Fixed selector examples in `Compiler/Selectors.lean`.
- CI cross-checks selectors against `solc --hashes`.
- Selector fixture checks still run as defense in depth.

### Kernel-computable mapping-slot Keccak-256

**Location**: `Compiler/Proofs/MappingSlot.lean`, `Compiler/Keccak/*.lean`

**Role**:
Computes mapping storage slots as `keccak256(abi.encode(key, baseSlot))` using
the same kernel-computable Keccak engine. The output-length bound is proved
structurally via `Compiler/Keccak/SpongeProperties.lean`.

**What we trust**:
- The kernel Keccak implementation matches the EVM's keccak256 (CI cross-checked).
- Two different inputs won't hash to the same slot (standard cryptographic
  assumption — Solidity makes the same one).

**Soundness controls**:
- Mapping-slot abstraction boundary checks in CI.
- End-to-end regression suites that exercise mapping reads/writes.
- CI cross-checks kernel Keccak output against FFI Keccak output.

### Kernel-computable source-semantics `keccak256(offset, size)`

**Location**: `Compiler/Proofs/IRGeneration/SourceSemantics.lean`
(`keccakMemorySlice`, `memorySliceBytesBE`, and the `.keccak256` arms of
`evalExpr` / `evalExprWithHelpers`).

**Role**:
The executable source semantics evaluates `Expr.keccak256 offset size` by reading
the `RuntimeState` memory as 256-bit words at `offset, offset+32, …`,
concatenating them big-endian, truncating the result to `size` bytes, and hashing
with the in-tree `KeccakEngine.keccak256`. Previously this expression evaluated to
`none` (modeled as a revert), so any contract performing a native `keccak256` fell
outside the modeled fragment; it is now executably modeled.

**What we trust** (`keccak256_memory_slice_matches_evm`):
Verity's compiled output writes scratch memory in whole 32-byte words (`mstore`),
so reading whole words and truncating the big-endian concatenation to `size` bytes
reproduces the EVM's byte-addressed `keccak256(offset, size)` preimage exactly. The
`RuntimeState` memory is word-keyed, so sub-word / byte-granular aliasing is not
modeled; this is faithful for the word-aligned access shape Verity emits and is the
same assumption already surfaced in `--trust-report` for `Expr.keccak256`.

**Soundness controls**:
- Reuses the same kernel-computable `KeccakEngine.keccak256` that CI cross-checks
  against FFI/EVM keccak; no new hash implementation is introduced.
- `keccakMemorySlice` is an ordinary computable definition, not an axiom: it adds
  no `axiom`/`sorry` to the trust surface.

## EVMYulLean Runtime Semantics (Non-Axiom)

**Location**:
`Compiler/Proofs/YulGeneration/Backends/EvmYulLean*.lean`,
`lake-manifest.json`, `artifacts/evmyullean_fork_audit.json`

**Role**:
EVMYulLean is the authoritative Yul runtime target for the safe-body EndToEnd
retargeting path. This is not a Lean axiom: Verity proves the adapter, builtin
bridge, recursive target equality, safe-body closure, and public EndToEnd
wrappers in Lean, then trusts that the pinned EVMYulLean execution model matches
the EVM.

**What we trust**:
- The pinned `lfglabs-dev/EVMYulLean` fork matches the intended EVM/Yul
  semantics inherited from upstream `NethermindEth/EVMYulLean`.
- The audited fork delta remains non-semantic unless explicitly reviewed.

**Soundness controls**:
- `make check` validates the fork-audit artifact against `lake-manifest.json`.
- `make test-evmyullean-fork` rechecks the fork audit, checks the adapter
  report, rebuilds the native transition harness, the public EndToEnd
  EVMYulLean target, and the concrete `native_decide` bridge-equivalence
  tests.
- `.github/workflows/evmyullean-fork-conformance.yml` runs the conformance probe
  weekly; scheduled or manual failures fail the workflow and
  open or update a GitHub issue for drift triage.

## External Call Module (ECM) Assumptions

When your contract calls an external contract (like an ERC-20 token), Verity
can't prove that the *other* contract works correctly. Instead, it documents
the assumption: "we assume this address implements the expected interface."

These are **not** proof-system axioms — they are interface assumptions scoped
to contracts that use the module. The compiler lists all of them at compile
time in `--verbose` output. Use `--deny-unchecked-dependencies` to make
compilation fail if any assumption hasn't been reviewed.

### Caller-frame preservation theorems

Independently of the ECM interface assumptions above, the *EVM frame
condition* that an external `CALL` cannot mutate the caller's storage,
transient storage, or memory outside the declared output buffer is now a
**theorem** of `Verity.EVM.Frame`, no longer an assumption. The relevant
results are:

- `Verity.EVM.Frame.external_call_preserves_caller_storage`
- `Verity.EVM.Frame.external_call_preserves_caller_transient_storage`
- `Verity.EVM.Frame.external_call_preserves_caller_memory_outside_output_buffer`
- `Verity.EVM.Frame.external_call_preserves_caller_memory` (disjoint-region form)
- their iterated-CALL variants `Verity.EVM.Frame.external_calls_preserve_*`

The theorems quantify universally over `Verity.EVM.Frame.CalleeResult`,
which is the observational interface of any EVM callee program. Downstream
contract proofs can consume these theorems directly to discharge the EVM
frame condition without re-stating it.

The abstract memory model on which these theorems compose lives at
`Verity.EVM.MemoryModel`; the standard solc memory-layout schema and the
call-buffer-disjoint-from-heap theorem live at `Verity.EVM.Layout`.

### Standard Module Assumptions

| Module | Assumption | Meaning |
|--------|------------|---------|
| `ERC20.safeTransfer` | `erc20_transfer_interface` | Target implements ERC-20 `transfer(address,uint256)` |
| `ERC20.safeTransferFrom` | `erc20_transferFrom_interface` | Target implements ERC-20 `transferFrom(address,address,uint256)` |
| `ERC20.safeApprove` | `erc20_approve_interface` | Target implements ERC-20 `approve(address,uint256)` |
| `ERC20.solmateSafeTransfer` | `erc20_solmate_safe_transfer_interface` | Target implements ERC-20 `transfer(address,uint256)`; optional-return acceptance follows Solmate SafeTransferLib |
| `ERC20.solmateSafeTransferFrom` | `erc20_solmate_safe_transferFrom_interface` | Target implements ERC-20 `transferFrom(address,address,uint256)`; optional-return acceptance follows Solmate SafeTransferLib |
| `ERC20.legacyStringSafeTransfer` | `erc20_legacy_string_safe_transfer_interface` | Target implements ERC-20 `transfer(address,uint256)`; uses legacy string `Error("...")` reverts + extcodesize check (Morpho-style) |
| `ERC20.legacyStringSafeTransferFrom` | `erc20_legacy_string_safe_transferFrom_interface` | Target implements ERC-20 `transferFrom(address,address,uint256)`; uses legacy string `Error("...")` reverts + extcodesize check (Morpho-style) |
| `ERC20.balanceOf` | `erc20_balanceOf_interface` | Target implements `balanceOf(address)` and returns a `uint256` |
| `ERC20.allowance` | `erc20_allowance_interface` | Target implements `allowance(address,address)` and returns a `uint256` |
| `ERC20.totalSupply` | `erc20_totalSupply_interface` | Target implements `totalSupply()` and returns a `uint256` |
| `ERC4626.previewDeposit` | `erc4626_previewDeposit_interface` | Target implements `previewDeposit(uint256)` and returns a `uint256` |
| `ERC4626.previewMint` | `erc4626_previewMint_interface` | Target implements `previewMint(uint256)` and returns a `uint256` |
| `ERC4626.previewWithdraw` | `erc4626_previewWithdraw_interface` | Target implements `previewWithdraw(uint256)` and returns a `uint256` |
| `ERC4626.previewRedeem` | `erc4626_previewRedeem_interface` | Target implements `previewRedeem(uint256)` and returns a `uint256` |
| `ERC4626.convertToAssets` | `erc4626_convertToAssets_interface` | Target implements `convertToAssets(uint256)` and returns a `uint256` |
| `ERC4626.convertToShares` | `erc4626_convertToShares_interface` | Target implements `convertToShares(uint256)` and returns a `uint256` |
| `ERC4626.totalAssets` | `erc4626_totalAssets_interface` | Target implements `totalAssets()` and returns a `uint256` |
| `ERC4626.asset` | `erc4626_asset_interface` | Target implements `asset()` and returns an `address` |
| `ERC4626.maxDeposit` | `erc4626_maxDeposit_interface` | Target implements `maxDeposit(address)` and returns a `uint256` |
| `ERC4626.maxMint` | `erc4626_maxMint_interface` | Target implements `maxMint(address)` and returns a `uint256` |
| `ERC4626.maxWithdraw` | `erc4626_maxWithdraw_interface` | Target implements `maxWithdraw(address)` and returns a `uint256` |
| `ERC4626.maxRedeem` | `erc4626_maxRedeem_interface` | Target implements `maxRedeem(address)` and returns a `uint256` |
| `ERC4626.deposit` | `erc4626_deposit_interface` | Target implements `deposit(uint256,address)` and returns a `uint256` |
| `Oracle.oracleReadUint256` | `oracle_read_uint256_interface` | Target implements the selected oracle read interface and returns a `uint256` |
| `Precompiles.ecrecover` | `evm_ecrecover_precompile` | EVM precompile at address 0x01 behaves per Yellow Paper |
| `Precompiles.sha256Memory` / `Precompiles.sha256` | `evm_sha256_precompile` | EVM precompile at address 0x02 behaves per Yellow Paper |
| `Precompiles.bn256Add` | `evm_bn256_add_precompile` | EVM precompile at address 0x06 behaves per EIP-196 (BN254 point addition) |
| `Precompiles.bn256ScalarMul` | `evm_bn256_scalar_mul_precompile` | EVM precompile at address 0x07 behaves per EIP-196 (BN254 scalar multiplication) |
| `Precompiles.bn256Pairing` | `evm_bn256_pairing_precompile` | EVM precompile at address 0x08 behaves per EIP-197 (BN254 optimal-Ate pairing) |
| `Callbacks.callback` | `callback_target_interface` | Callback target processes ABI-encoded arguments correctly |
| `Calls.withReturn` | `external_call_abi_interface` | Target contract function matches declared selector and ABI |
| `Calls.callWithValue` / `Calls.callWithValueBytes` | `generic_call_with_value_interface` | Target accepts caller-provided calldata and ETH value; failures bubble returndata |
| `Calls.bubblingValueCall` / `Calls.bubblingValueCallNoOutput` | `generic_low_level_value_call_interface` | Generic low-level `call` mechanics are emitted; calldata and successful returndata meaning remain package assumptions |
| `Calls.selfDelegateMulticallBytes` | `self_delegate_multicall_bytes_revert_bubbling` | Trusted ECM boundary for Solidity-style `multicall(bytes[])`: generated Yul is audited to reject malformed/wrapping offsets, self-`delegatecall` each calldata payload, and bubble revert returndata exactly; full non-empty multicall semantics remain assumed |
| `Hashing.abiEncodeStaticWords` | `keccak256_memory_slice_matches_evm`, `abi_standard_static_word_layout` | Static ABI words are laid out contiguously before Keccak |
| `Hashing.abiEncodePackedWords` / `Hashing.abiEncodePacked` | `keccak256_memory_slice_matches_evm`, `abi_packed_static_word_layout` | Static packed words are laid out contiguously before Keccak |
| `Hashing.abiEncodeStaticArray` | `keccak256_memory_slice_matches_evm`, `abi_standard_dynamic_array_static_element_layout` | Single dynamic-array ABI encoding with static-width elements is laid out before Keccak |
| `Hashing.abiEncodePackedStaticSegments` | `keccak256_memory_slice_matches_evm`, `abi_packed_static_segment_layout` | Static packed byte-width segments are laid out before Keccak |
| `Hashing.eip712Digest` | `keccak256_memory_slice_matches_evm`, `eip712_digest_layout` | Final EIP-712 typed-data preimage is laid out as `0x1901 || domainSeparator || structHash` before Keccak |
| `Hashing.sha256PackedWords` / `Hashing.sha256Packed` | `evm_sha256_precompile`, `abi_packed_static_word_layout` | Static packed words are laid out before SHA-256 precompile call |
| `Hashing.sha256PackedStaticSegments` | `evm_sha256_precompile`, `abi_packed_static_segment_layout` | Static packed byte-width segments are laid out before SHA-256 precompile call |

### Test-Only ECM Assumptions

| Fixture | Assumption | Meaning |
|---------|------------|---------|
| `Compiler.CompileDriverTest` | `test_call_interface` | Synthetic compile-driver fixture for ECM trust reporting |
| `Compiler.CompileDriverTest` | `ctor_hook_interface` | Synthetic constructor fixture for ECM trust reporting |

### Third-Party Module Assumptions

Third-party ECMs (external Lean packages) document their assumptions in their own
`AXIOMS.md`. All assumptions — standard and third-party — are listed at compile
time. See `docs/EXTERNAL_CALL_MODULES.md` for details.

**Risk**: Low. These are interface assumptions (not proof-system extensions)
scoped to contracts that use the module.

## Non-Axiom: Arithmetic

All 25 pure EVM arithmetic builtins have universal bridge equivalence lemmas
(all 25 fully proven).
The proofs show that Verity's arithmetic matches EVM arithmetic (wrapping at
2^256) for *all* possible inputs, not just test cases. The EVMYulLean bridge
currently has universal equivalence lemmas for 25 of them (`add`, `sub`, `mul`,
`div`, `mod`, `addmod`, `mulmod`, `exp`, `sdiv`, `smod`, `lt`, `gt`, `slt`, `sgt`, `eq`, `iszero`, `and`, `or`,
`xor`, `not`, `shl`, `shr`, `sar`, `signextend`, `byte`),
with no remaining pure builtins relying only on concrete bridge checks.

Additionally, 8 higher-level expression operators have proven compilation
correctness in the `ExprCompileCore` fragment: `min`, `max`, `ceilDiv`, `ite`
(conditional), `wMulDown`, `wDivUp`, `mulDivDown`, and `mulDivUp`. See
[`docs/ARITHMETIC_PROFILE.md`](docs/ARITHMETIC_PROFILE.md) for the full
specification.

## Consumer Intrinsic Obligations (from verity_intrinsic)

Intrinsics do not add project-level Verity axioms. Each `verity_intrinsic`
declaration names a consumer-owned obligation in its `obligation [...]` clause
and records that obligation next to the generated consumer semantic wrapper.
While that obligation is `assumed`, the consumer repository must document it in
its own `AXIOMS.md` or equivalent trust-boundary document.

For example, a Tamago CLZ intrinsic should document the consumer-side
`clz_matches_eip7939` assumption: the Lean `semantics` function used by Tamago
proofs matches the EIP-7939 opcode emitted as `verbatim_1i_1o(hex"1e", x)` on
chains that support Osaka-or-later execution semantics.

These obligations are outside this registry because they are not axioms in the
Verity project. Future consumer trust reports should surface them
machine-readably; until that integration exists, review them by grepping
consumer code for `verity_intrinsic`.

The Verity-side proof module `Compiler.Proofs.IRGeneration.IntrinsicProofs`
proves only compiler-owned plumbing around the generic intrinsic path:
argument scope accounting, verbatim/builtin lowering shape, fork-order facts,
arity rejection, and the fail-closed `min_fork` predicate used by the compiler
fork gate. It adds no axiom asserting that any emitted opcode implements the
declared consumer semantics. The current end-to-end proven fragment remains
fail-closed over intrinsics: `SupportedSpec` and helper-aware source semantics
classify `Expr.intrinsic` as unsupported/unmodeled until an opcode semantics
proof exists.

## Trust Summary

- Active project-level axioms: 0
- Production blockers from project-level axioms: 0
- Consumer intrinsic obligations: owned and documented by consumer packages
- Enforcement: `scripts/check_axioms.py` ensures this file tracks exact source locations.
- All internal compiler functions are proven to terminate (no axioms involved).
- The macro front-end and typed-IR pipeline do not use any
  axioms. The typed-IR compiler has zero `sorry`.

## Maintenance Rule

Any commit that adds, removes, renames, or moves a project-level axiom must
update this file in the same commit. Any commit that changes intrinsic trust
semantics must update this file, [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md),
and [AUDIT.md](AUDIT.md).

If this file is stale, trust analysis is stale.

**Last Updated**: 2026-05 (intrinsics addition)
