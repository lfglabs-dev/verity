# Vault from Solidity

This self-contained example imports an existing Solidity contract into Lean and
proves properties directly about the imported definitions. It does not depend on
the handwritten `Contracts/Vault` example.

## File map

| File | Role |
| --- | --- |
| `Vault.sol` | The original Solidity implementation. |
| `Importer/Importer.lean` | Runs pinned solc, validates typed AST/storage layout, translates, and registers checked Verity definitions. |
| `VaultFromSolidity.lean` | Points the importer at `Vault.sol`. |
| `Spec.lean` | Human-written requirements for the imported contract. |
| `Proofs/Execution.lean` | Proofs that the imported contract satisfies those requirements. |
| `Importer/scripts/solidity_importer_test.py` | Maintainer acceptance tests; not a developer translation step. |

## Developer workflow

1. Keep or edit `Vault.sol`.
2. Declare its import in `VaultFromSolidity.lean`.
3. Write the required behavior in `Spec.lean`.
4. Prove it in `Proofs/Execution.lean`.
5. Run `lake build VaultFromSolidity` and reload the Lean editor after Solidity changes.

`Importer.lean` invokes pinned solc with `--standard-json` and
`--no-import-callback`, then parses and validates its typed AST and storage
layout in Lean. Explicit `translateExpr` / `translateStmt` cases construct
transparent, kernel-checked `Verity.Contract` definitions directly in memory.
There is no Python frontend, custom serialized IR, generated Lean source, or
bytecode.

The current proof of concept accepts only this registered Vault and a deliberately
small Solidity subset. The importer remains a trusted translation boundary: the
Lean kernel proves the stated properties of the imported definitions, not a
general Solidity-to-Verity or bytecode equivalence theorem.
