# Stateful Midnight differential campaign

Run from the Verity checkout, with the differential Python dependencies,
Foundry v1.5.0 and the checksum-pinned solc 0.8.34 installed:

```sh
PYTHONPATH=scripts python3 -m solidity_differential.check_midnight_admin \
  --midnight-repo /path/to/midnight-at-96d31343 \
  --output .lake/midnight-admin-seed-2514 \
  --transactions 256 --seed 2514
```

The command requires the corpus commit
`96d31343e993329e7a593dde46516a2c0cbcd142` and clean tracked production
sources. It compiles the original `src/Midnight.sol` and its real imports,
imports ten administrative and authorization entry points into one model,
and executes successive transactions through solc bytecode, Denote and
Verity-compiled bytecode. It uses the existing discovery/replay comparator
for exact status, return/revert bytes, every touched slot and ordered events.
Each generated driver lives inside the Lake workspace. Output directories
must be fresh; previous results are retained.

The deterministic prefix exercises role handover, invalid fee parameters,
delegation, revocation and decreasing consumed amounts. Random transactions
then vary callers, roles, tokens, groups, boundary values and authorization.
`campaign.json` records the selected signatures, source hashes, exact compiler
hash, implementation snapshot, initial storage, transactions and observations.
An ordinary divergence exits 1 after shrinking and replaying it; tool failures
are errors and never count as matched Solidity reverts.

To test the instrument, repeat with `--mutant drop-events`. That deliberately
removes model event statements, leaving the source contract intact. It must
exit 1, record an event divergence and produce a reproducible reduced sequence.
A surviving mutant is an instrumentation error.

This is a partial Midnight campaign. It covers ten already importable entry
points, not all 45 required functions, external calls or market creation.
Constructor equivalence is not claimed: all routes receive the same explicit
initial storage, with the deployer installed as configurator using solc's
actual storage-layout slot. Source deployment still runs the actual constructor;
deployment logs are outside the transaction observations. The result neither
changes the coverage denominator nor satisfies the complete-Midnight sustained
campaign criterion. There is no source rewrite or replacement Solidity fixture.
