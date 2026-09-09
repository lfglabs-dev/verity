# One Vault, two implementations

Choose how to write the contract; reuse the same specification and proof file.

| File | Role |
| --- | --- |
| `Vault.lean` | Write the Vault directly with `verity_contract`. |
| `../../examples/solidity/Vault.sol` | Existing Solidity implementation, unchanged. |
| `Solidity.lean` | One `solidity_contract` declaration imports that Solidity file. |
| `Implementations.lean` | Select `.verity` or `.solidity` at the same typed external-call boundary. |
| `Spec.lean` | Shared requirements, including the original accounting specs. |
| `Proofs/Execution.lean` | One proof suite parameterized by the selected implementation. |

For example, `Execution.deposit_existing_spec .verity` and
`Execution.deposit_existing_spec .solidity` are the **same theorem and proof**,
instantiated with different implementations. Neither branch assumes an unproved
correspondence; Lean checks both bodies. Existing `Proofs/Correctness.lean`
continues to check the original getter proofs.

## Developer workflow

1. Keep the contract in Solidity, or write it directly in Verity.
2. For Solidity, add the thin import declaration shown in `Solidity.lean`.
3. Write/reuse `Spec.lean`, then check the proofs with `lake build SolidityVault`.
4. After editing Solidity, rebuild and reload the Lean editor; live Solidity
   watching is not implemented. See the root README for pinned-solc setup.

The POC is registered for this Vault only, not arbitrary Solidity projects.

Under the hood: `solc` resolves Solidity types/references;
`scripts/solidity_contract.py` validates its AST and prepares structured JSON;
`Verity/Solidity.lean` turns it into checked Verity definitions in memory.
The separate `scripts/check_solidity_contract.py` is the **maintainer test suite**,
not a second developer translation step. No generated model `.lean` or bytecode.

## Matching behavior, not just names

Verity already rejects ETH on nonpayable external calls in its compiler dispatcher
(`Compiler/CodegenCommon.lean`, `callvalueGuard`/`dispatchBody`). Its bare Lean
function definitions represent bodies. `Implementations.lean` exposes this guard
explicitly for shared proofs; the imported entrypoints already include it.
This adapter is not a proved full compiler-dispatch bridge.

Both versions use matching withdrawal custom errors (`InsufficientShares()`, etc.)
and deposit write order. Shared proofs cover success, frame preservation,
nonpayability, withdrawal errors and late-overflow rollback, using the same
specification and hypotheses. Solidity's public mapping getter corresponds to
native `balanceOf` in the shared interface. Error labels and logical storage are
model representations; exact revert bytes, deployment and full Solidity/EVM
correspondence are not proved. The importer remains trusted.
