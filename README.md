<p align="center">
  <img src="verity.svg" alt="Verity" width="200" />
</p>

<h1 align="center">Verity</h1>

<p align="center">
  <strong>A formally verified smart contract compiler for Ethereum, written in Lean 4.</strong><br/>
  Documentation: <a href="https://veritylang.com">veritylang.com</a> &nbsp;·&nbsp; Paper: <a href="https://lfglabs.dev/papers/verity.pdf">verity.pdf</a> &nbsp;·&nbsp; Built by <a href="https://lfglabs.dev">LFG Labs</a>
</p>

<p align="center">
  <a href="https://veritylang.com"><img src="https://img.shields.io/badge/docs-veritylang.com-0a7d7d.svg" alt="Verity documentation"></a>
  <a href="https://github.com/lfglabs-dev/verity/blob/main/LICENSE.md"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="MIT License"></a>
  <a href="https://github.com/lfglabs-dev/verity"><img src="https://img.shields.io/badge/built%20with-Lean%204-blueviolet.svg" alt="Built with Lean 4"></a>
  <a href="https://github.com/lfglabs-dev/verity/blob/main/docs/VERIFICATION_STATUS.md"><img src="https://img.shields.io/badge/verification%20status-live-brightgreen.svg" alt="Verification status"></a>
  <a href="https://github.com/lfglabs-dev/verity/actions"><img src="https://img.shields.io/github/actions/workflow/status/lfglabs-dev/verity/verify.yml?label=verify" alt="Verify"></a>
</p>

---

**Verity** is a formally verified smart contract compiler written in [Lean 4](https://lean-lang.org/). You write contracts in an embedded DSL, state what they should do, prove those properties hold, and compile to EVM bytecode. The compiler itself is proven to preserve semantics across three verified layers. Full documentation lives at [**veritylang.com**](https://veritylang.com).

## Proof-only Solidity Vault import (POC)

`Contracts/VaultFromSolidity/VaultFromSolidity.lean` imports the colocated
`Vault.sol` with `solidity_contract VaultFromSolidity from "Vault.sol"`.
The Lean frontend invokes pinned solc 0.8.33 for typed AST and storage layout,
validates them, and parses them into the closed, intrinsically typed inductive in
`Contracts/VaultFromSolidity/Importer/Syntax.lean`. `Importer/Semantics.lean`
gives each construct its one meaning, and each entry point is registered in
memory as `Fn.meaning` applied to its parsed term, as a transparent,
kernel-checked `Verity.Contract` definition. There is no Python
frontend, custom serialized IR, generated `.lean`, CompilationModel, or
bytecode. The example is independent of the
handwritten `Contracts/Vault` contract.

The importer elaborates a kernel-checked `Storage` structure named after the
Solidity state variables, so `Spec.lean` reads like the contract instead of
naming raw slots:

```lean
-- before
def solvent (s : ContractState) : Prop := s.readSlot 0 = s.readSlot 1

-- after
def solvent (v : Storage) : Prop := v.totalAssets = v.totalSupply

def deposit_spec (amount : Uint256) (caller : Address) (pre post : Storage) : Prop :=
  post.totalAssets = pre.totalAssets + amount ∧
  post.totalSupply = pre.totalSupply + amount ∧
  post.shareBalances caller = pre.shareBalances caller + amount ∧
  ∀ other, other ≠ caller → post.shareBalances other = pre.shareBalances other
```

`view` constructs that `Storage` from the `<var>Slot` handles solc's storage
layout produced, so reordering the Solidity declarations moves the slots without
touching the spec, and renaming a variable makes the spec fail to elaborate.
`#print view` shows the `readSlot`/`readMap` unfolding. The importer also
registers a deterministic entry-point relation `step`. `Proofs/ExecutionProof.lean`
proves each successful call meets its spec and that `solvent` is preserved by
`step` (`solvent_invariant`).

With the Lean/package prerequisites installed, put an official solc 0.8.33
build at `.lake/solidity-import/solc` (`make setup-solc-importer` fetches the
host platform's `list.json` from binaries.soliditylang.org, checks the
published SHA-256 against the committed pin, and installs that binary). The
importer allowlists the official linux-amd64 and macosx-amd64 digests; Linux
CI still uses linux-amd64. Then run:

```sh
lake build VaultFromSolidity
python3 Contracts/VaultFromSolidity/Importer/scripts/solidity_importer_test.py
lake build SolidityImportSmokeInheritance
python3 Contracts/SolidityImportSmoke/Inheritance/scripts/inheritance_test.py
```

The Vault acceptance script uses disposable copies for source mutations, fail-closed
rejection, content-based Lake freshness, compiler/importer/build-policy
invalidation, declaration-registration rollback, and an audit of every Vault
theorem. It never mutates the original Solidity file. The inheritance smoke
(`Contracts/SolidityImportSmoke/Inheritance`) covers same-file `is` bases, C3
linearization including a diamond, virtual dispatch, `super` (target C3, not
the defining-contract AST id), opaque fields, and internal calls (`Expr.call`
is view/pure only); `inheritance_test.py` is the matching focused suite.
Save Solidity, rebuild this dedicated target, then reload the Lean editor:
an already-open editor snapshot does not automatically watch `.sol` changes.
See [the trust boundary](TRUST_ASSUMPTIONS.md#proof-only-solidity-vault-import).

## Verification status

All proofs are machine-checked by the Lean kernel. CI rebuilds the proof development on every commit, and repository checks enforce that no proof is left incomplete (no `sorry`) and that the compiler proof stack carries 0 axioms (see [AXIOMS.md](AXIOMS.md)). Verification is scoped rather than total: the generic compiler theorems cover an explicitly documented fragment of the language, and the precise boundary between what is proven and what is trusted is maintained in [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md).

A detailed proof inventory — theorem status, per-contract results, and test coverage — is regenerated from the codebase and tracked in [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md). All checks are reproducible locally (see [Quick start](#quick-start)).

## What is verified

Verity proves that compilation preserves behavior at three stages. Each layer is a machine-checked Lean theorem.

**Layer 1** (EDSL to CompilationModel): the `verity_contract` macro generates both an executable Lean program and a compiler-facing model from a single definition. Per-contract bridge theorems prove they agree.

**Layer 2** (CompilationModel to IR): a generic whole-contract theorem covers the supported fragment with zero axioms. No per-contract proof effort needed. Internal helper calls now exist at the source level, and helper-summary proof reuse is available in source-semantics lemmas, but that reuse is not yet fully consumed through the generic body/IR theorem path. ECMs, typed interface calls, external calls, and low-level call/returndata mechanics are trust-reported or compiler-supported rather than fully proof-modeled. Constructors, fallback/receive, events/logs, typed errors, proxy/delegatecall, local obligations, and richer storage-layout features remain outside the generic proof fragment or partial. `forEach` support is deliberately partial: zero-bound loops with supported bodies and arbitrary literal-bound empty-body loops are proved, while positive non-empty loop bodies remain outside the current theorem.

**Layer 3** (IR to Yul): all statement types are proven equivalent. The dispatch bridge is an explicit theorem hypothesis, not an axiom.

The Yul-to-bytecode step is handled by `solc` (v0.8.33, pinned) and is not verified by Verity. See [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md) for the complete trust boundary.

## How it works

```
verity_contract Counter where
  storage count : Uint256 := slot 0
  function increment () : Unit := do
    let current <- getStorage count
    setStorage count (add current 1)
```

```lean
theorem increment_correct (s : ContractState) :
    let s' := ((increment).run s).snd
    s'.storage 0 = add (s.storage 0) 1 := by rfl
```

The proof passes by `rfl` (reflexivity): Lean's kernel evaluates both sides and confirms they are definitionally equal. No external solver, no bounded model checker, no trust in anything beyond Lean's type theory.

## Quick start

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env
git clone https://github.com/lfglabs-dev/verity.git && cd verity
lake build                        # verify all proofs (~20 min first build)
make check                        # run full CI validation suite
FOUNDRY_PROFILE=difftest forge test  # differential tests: EDSL vs EVM
```

## How Verity compares

| | Certora | Halmos | Verity |
|---|---|---|---|
| **Approach** | Bounded model checking | Symbolic execution | Theorem proving in Lean 4 |
| **Proof scope** | Bounded (configurable depth) | Bounded (path explosion) | Unbounded (all inputs, all paths) |
| **Compiler trust** | Trusts solc entirely | Trusts solc entirely | Verifies 3 compilation layers |
| **Best for** | Production audits at scale | Bug-finding in Foundry | High-assurance contracts |

Verity is complementary to these tools. It is for cases where you need mathematical certainty across all inputs and all execution paths.

## Documentation

| Resource | Description |
|----------|-------------|
| [veritylang.com](https://veritylang.com/) | Full documentation site |
| [Solidity to Verity](https://veritylang.com/guides/solidity-to-verity) | Practical syntax and semantic mappings for Solidity ports |
| [Production Solidity Patterns](https://veritylang.com/guides/production-solidity-patterns) | Agent guidance for production ports, reusable Verity features, and oracle/spec boundaries |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | Contributor map for source features, proof layers, trust surfaces, and regression checks |
| [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md) | Theorem counts, proof status, test coverage |
| [docs/INTRINSICS.md](docs/INTRINSICS.md) | Consumer-owned opcode bindings and their trust model |
| [docs/LOW_LEVEL_YUL.md](docs/LOW_LEVEL_YUL.md) | Policy for typed low-level primitives vs. raw Yul escape hatches |
| [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md) | What is verified vs. what is trusted |
| [AXIOMS.md](AXIOMS.md) | Documented axioms (currently 0) |
| [AUDIT.md](AUDIT.md) | Trust-boundary audit evidence and CI guards |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Contribution guidelines |

### Research

- [Verity: A Formally Verified Smart Contract Compiler](https://lfglabs.dev/papers/verity.pdf)
- [Verity Benchmark: AI-Driven Proof Generation](https://lfglabs.dev/research/verity-benchmark)
- [What is a formal proof?](https://lfglabs.dev/research/what-is-a-formal-proof)

## Support

Verity is a public good. If you'd like to support the project, you can donate via Giveth:

[verity: Smart Contracts Security for the Age of AI](https://giveth.io/project/verity:-smart-contracts-security-for-the-age-of-ai)
