# Audit Trail: P-ACCOUNT-1 / P-ADDRESS-1

**Solidity pin:** `17005714f151e5502c559932319a3f2f74ac2436`
**Checkpoint:** `38895d80`
**Branch base (main):** `caad1ef5e297202636e6fe643afa88fe8a62d618`
**Date:** 2026-09-08

## Status

Specification and tests — **NOT** claimed as a certified compile.
Prod archive-forward (HEAD `4622ddd8`) is **uncertified**.

## What is proven (Lean 4.12.0, zero `sorry`)

### P-ADDRESS-1 (`PAddress1.lean`)

| Property | Theorem | Kind |
|---|---|---|
| Address values bounded to 160 bits | `Address.bounded` | Safety |
| Pack/unpack lossless roundtrip | `Address.roundtrip` | Correctness |
| Out-of-range rejection | `Address.ofNat?_rejects` | Safety |
| toNat injectivity | `Address.toNat_injective` | Correctness |
| ofNat? value recovery | `Address.ofNat?_val` | Correctness |
| Auth recovery determinism | `auth_deterministic` | Determinism |
| Batch subset property | `validateBatch_subset` | Correctness |
| Batch bound preservation | `validateBatch_bounded` | Safety |

### P-ACCOUNT-1 (`PAccount1.lean`)

| Property | Theorem | Kind |
|---|---|---|
| Fee deduction conserves balance | `deductFee_conserves` | Conservation |
| Fee deduction preserves nonce | `deductFee_nonce_preserved` | Frame |
| Insufficient balance → rejection | `deductFee_insufficient` | Safety / underflow witness |
| Credit computes correct sum | `credit_sum` | Correctness |
| Credit overflow → rejection | `credit_overflow_witness` | Safety / overflow witness |
| Credit preserves nonce | `credit_nonce_preserved` | Frame |
| Fee-then-claim roundtrip | `fee_claim_roundtrip` | Conservation law |
| OutOfGas beats Revert | `outofgas_beats_revert` | Panic precedence |
| OutOfGas beats Success | `outofgas_beats_success` | Panic precedence |
| Revert beats Success | `revert_beats_success` | Panic precedence |
| Beats is irreflexive | `beats_irrefl` | Well-ordering |
| Beats is asymmetric | `beats_asymm` | Well-ordering |
| Beats is transitive | `beats_trans` | Well-ordering |
| Resolve picks higher-priority | `resolve_picks_higher` | Precedence |
| Pack/unpack roundtrip | `pack_unpack_roundtrip` | Correctness |
| Unpack/pack roundtrip | `unpack_pack_roundtrip` | Correctness |
| Batch nil identity | `applyBatch_nil` | Batch |
| Batch cons (some) | `applyBatch_cons_some` | Batch |
| Batch cons (none) | `applyBatch_cons_none` | Batch |
| Batch append decomposition | `applyBatch_append` | Batch / associativity |
| Auth required for apply | `verifyAndApply_requires_auth` | Auth |

## What is tested (concrete + property)

- Fee deduction: success, insufficient, exact balance
- Credit: success, overflow rejection
- Fee-then-claim roundtrip conservation
- Panic precedence: all pairwise orderings, resolve function
- Packed storage roundtrip on concrete values
- Batch: multi-op success, mid-batch failure propagation
- Auth: correct sender passes, wrong sender rejected
- Mutation canaries: bound constants, address space size

## What is NOT proven / NOT claimed

- EVM bytecode equivalence (transport-dependent; out of scope)
- Prod archive-forward correctness (HEAD `4622ddd8` is uncertified)
- secp256k1-specific signature recovery (auth is abstract/transport-independent)
- Gas metering or execution-trace fidelity
- Storage trie or Merkle proof verification
- Cross-contract call semantics

## Design notes

- Transport-independent: no network-layer or serialisation-format assumptions
- Auth is modelled as an opaque `recover` function, not tied to any curve
- Specs are independent of implementation — they define *what* must hold, not *how*
- No tautologies: every theorem has a non-trivial proof obligation
- Panic precedence uses a strict total order on `ExecOutcome` with proved irreflexivity, asymmetry, and transitivity
