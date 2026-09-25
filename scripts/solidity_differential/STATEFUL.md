# Stateful differential adapter protocol

The stateful instrument is under construction. `stateful.py` defines strict
observations and replay/reduction; `anvil.py` executes real transactions on an
owned Foundry Anvil node. `denote.py` invokes the actual Lean sequence runner;
`check_stateful.py` compares all three routes on a handwritten scalar model
paired with Solidity, with configurable seed and transaction count. Passing the adapter checks is not evidence
that an imported non-view function agrees across all three routes.

Run the complete instrument from the repository root (also run in CI):

```sh
scripts/check_solidity_differential.sh --stateful --cases 64 --seed 2449 --output .lake/import-differential/stateful
```

This builds the Lean smoke modules, then runs protocol, adapter, mock, rejection,
mutation and all three equivalent-source campaigns. Each run requires a fresh
output directory and retains its evidence. Individual checks use the same Python
environment as the differential campaigns:

```sh
PYTHONPATH=scripts python3 -m unittest scripts/test_solidity_stateful.py
PYTHONPATH=scripts python3 -m solidity_differential.check_anvil
PYTHONPATH=scripts python3 -m solidity_differential.check_mocks
PYTHONPATH=scripts python3 -m solidity_differential.check_stateful --transactions 256 --seed 2449
PYTHONPATH=scripts python3 -m solidity_differential.check_stateful_mutations
PYTHONPATH=scripts python3 -m solidity_differential.check_denote_rejections
```

These checks require the pinned solc used by the existing differential harness,
Foundry Anvil, and the harness Python dependencies. They preserve solc inputs,
outputs, receipts, call traces, prestate traces and observations under `.lake`.
The Solidity files in `fixtures/` test the adapters and configurable mocks;
they are not presently imported CompilationModel conformance fixtures.

The campaign hashes local Lean sources, executable build artifacts (including
package and toolchain libraries), the driver and Python adapters before model
compilation. It records the Git revision and rechecks the complete file inventory
and stat identities before and after Denote runs. Any edit or rebuild invalidates
the campaign; this protects against concurrent local changes, not a malicious
filesystem that can forge inode and ctime metadata.

## Observations and replay

Every transaction observation has exactly `id`, `status`, `data`, `touched`,
`storage` and `events`. Data is canonical lowercase hex bytes. Storage identity
is an actual 20-byte account address and 32-byte slot; values are 32 bytes.
Events contain their actual emitting address, ordered topics and exact data.
Reverted transactions retain no committed events or writes, but their accessed
slots remain in the observation plan. Exceptional halts and instrumentation
failures are errors, not fabricated contract reverts.

`replay_three_routes` runs each adapter twice from its original fixture state.
Discovery collects the cumulative union of accessed and configured observation
slots across source, model and compiled routes. Replay samples every slot in
that plan after each transaction. Changes in an individual route between its
discovery and replay passes invalidate the run. Equality compares status,
return/revert bytes, post-storage and ordered events; optimized access traces
need not be identical across routes.

Each Anvil sequence specifies concrete deployment bytecode, initial storage,
and transaction sender, target, calldata, value, timestamp and block number.
Each call is a separate mined transaction so transient storage resets between
calls. A reduction deleting earlier calls fills the missing block positions
with empty blocks and preserves surviving timestamps/heights. It does not
preserve the deleted history's block hashes. Block-hash-sensitive fixtures will
need an explicit history policy shared by all three adapters.

`shrink_sequence` replays each candidate from the initial state. It preserves
the first divergence's observation categories and route equality pattern.
After exhausting deletion candidates it reports deletion-1-minimality, not a
globally smallest program or minimal argument values. A budget-limited result
explicitly declines that claim. The final candidate must reproduce the failure
in another replay; infrastructure errors propagate.

## Remaining integration requirements

The scalar Denote route retains reverted-path accesses and rolls back failed
transactions. Its trace is proved to agree with actual statement execution.
It rejects unsupported statements and nonempty events; exact byte-level event
encoding remains required. Its existing legacy event representation
and payload-erasing result projections cannot serve as exact EVM observations.
The campaign must also pin adapter/tool/configuration provenance, connect the
mock behaviors to Denote's external-world semantics, extend generated source variants and semantic mutation coverage to the
remaining construct families. The scalar generator supplies scoped-local and
early-return equivalents; the write-zero model mutation must disagree on real
storage and reduce to a single replayed transaction. The scalar campaign generates random transactions and automatically
replays and reduces any observed A/B/C divergence. No current adapter-only result discharges these gates.
