# Pinned real Midnight source caller

Regenerate/check with `scripts/check_native_midnight_source_capture.py`.
The three Solidity source keys and settings are identical to the original
staged source caller: real IdLib/IMidnight from Midnight 96d31343, solc 0.8.34,
viaIR, Osaka, optimizer 466, no metadata bytecode hash. Library input SHA-256
values are enforced. All generated files are compared byte-for-byte by --check.
The compiler SHA and version, source hashes and generated hashes are recorded.

The runtime contains the real ABI decoder for the dynamic Market tuple,
mapping write and IdLib deployment. Six inputs cover zero/one/two collateral
structs and mapping keys zero/maxuint. This is a source-bytecode instrument;
CREATE2 importer admission stays closed.

NativeMidnightSourceChecks checks native/pure hashing through the existing
checked prefix, then actual native creation, canonical creation, projected
Denote boundary and the whole native continuation. The global mutation script
runs it and detects three actual captured-bytecode/input mutations with replays.
check_native_midnight_source.py performs the fresh pinned-Foundry comparison,
including exact gas, trace operands/memory, slots/events, runtime and nonces.
Denote's explicit boundary projection is not a source-prefix equivalence proof.

The capture also derives 24 malformed inputs and NativeMidnightInvalidData.lean,
with 64-byte chunks so elaboration does not need elevated recursion limits.
NativeMidnightCollisionChecks adds 12 nonce/code collision continuations and
NativeMidnightInvalidChecks executes those 24 refusal inputs. Both are called
by the separate bounded global native-refusal check. Their separate Foundry drivers share only
the pinned-tool/native-launch helper and retain the original strict assertions.
