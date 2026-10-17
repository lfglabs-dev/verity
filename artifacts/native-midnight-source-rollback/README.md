# Successful creation, event, then caller revert

This independent capture imports the same real pinned IdLib/IMidnight sources as
the ordinary source caller, but emits Created(address) then reverts with
AfterDeploy(address) after successful deployment. Regenerate or check with
scripts/check_native_midnight_rollback_capture.py. The source/runtime capture
matches the original staged 1026-byte program exactly. It preserves the success,
collision and invalid-ABI source captures separately.

NativeMidnightRollbackChecks compares native creation with canonical creation
and projected Denote, then checks the actual full native custom-revert bytes and
gas. NativeMidnightRollbackRunner is the separate bounded global entrypoint.
The Foundry driver proves successful child return, nonzero CREATE2, exact LOG1
payload/topic and terminal revert, then observes committed root rollback of
mapping/code/nonces/events while retaining an unrelated slot. Native EVM.X's
revert result exposes no post-world; these checks do not claim a native-world
rollback theorem or whole imported-function equivalence. CREATE2 importer
admission remains closed.
