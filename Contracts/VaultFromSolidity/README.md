# Vault from Solidity

This self-contained example imports an existing Solidity contract into Lean and
proves properties directly about the imported definitions. It does not depend on
the handwritten `Contracts/Vault` example.

## File map

| File | Role |
| --- | --- |
| `Vault.sol` | The original Solidity implementation. |
| `Importer/scripts/solidity_importer.py` | Runs pinned solc, validates the supported AST and emits structured JSON. |
| `Importer/SolidityImporter.lean` | Implements `solidity_contract` and registers checked Verity definitions in Lean. |
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

The importer asks pinned solc for the typed AST and storage layout. The Python
frontend rejects unsupported constructs and emits a small JSON model. The Lean
importer converts that model into transparent, kernel-checked `Verity.Contract`
definitions directly in memory. It does not generate model `.lean` files or
bytecode.

The current proof of concept accepts only this registered Vault and a deliberately
small Solidity subset. The importer remains a trusted translation boundary: the
Lean kernel proves the stated properties of the imported definitions, not a
general Solidity-to-Verity or bytecode equivalence theorem.
