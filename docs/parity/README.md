# Solidity parity gap maps

Per-contract gap maps between production Solidity and the `verity_contract`
EDSL. Each file lists every top-level construct (state variables, structs,
events, errors, modifiers, functions) with one of:

- ✅ expressible in `verity_contract` today
- 🚧 expressible with a workaround (workaround noted)
- ❌ requires a new EDSL feature (feature named)

The maps are used to (a) prioritize feature work in issue
[#1724](https://github.com/lfglabs-dev/verity/issues/1724) and (b) drive a
planned nightly `contracts-smoke` CI job (not yet implemented) that will
compile each reference contract through Verity and assert no rows regress.

## Contents

- [`lido.md`](lido.md) — Lido StakingRouter v3 (Solidity 0.8.25 / 0.4.24)
- [`erc4337.md`](erc4337.md) — ERC-4337 v0.9 EntryPoint stack (eth-infinitism
  reference implementation)
- [`morpho.md`](morpho.md) — Morpho Blue singleton (`morpho-org/morpho-blue`)

## Convergent findings

Across all three contracts (423 constructs scored), the same top-3 missing
EDSL features dominate:

| Rank | Feature | Lido hits | 4337 hits | Morpho hits |
|---|---|---:|---:|---:|
| 1 | Narrow uints (`uint128`, `uint64`, `uint48`, `uint32`, `uint16`) | ~45 | 22 | ~15 |
| 2 | `abi.encode` / `encodePacked` / `encodeCall` codec | 6+ | 9 | 3 |
| 3 | First-class modifiers + inheritance (`is X, Y`) | ~30 | 8 | 4 |

Landing these three lands every reference contract north of 70% ✅ in one
wave; individual contract-specific gaps (EIP-712 for 4337/Morpho, `enum` for
Lido, flashloan callback for Morpho) come next.

## Updating a map

Any PR that changes a `verity_contract` construct row (adds support, changes
signature, deletes) MUST update the corresponding row in these files.
