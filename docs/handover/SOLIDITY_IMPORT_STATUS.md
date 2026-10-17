# Solidity Import Campaign Status (`coord/status`)

Last updated: 2026-10-17T10:53:00Z
Coordinator mission: `608d2555-9c5e-462c-b1c3-2c232703ccd9` (replaces `aae68584` / `300051ac` / `ebb2f1fe`)
Current `main` HEAD: `10f697bbb` (`#2503`)

---

## 1. Pinned Midnight Coverage Summary (`src/Midnight.sol` @ `96d31343e993329e7a593dde46516a2c0cbcd142`)

- **Total implemented functions in `Midnight` C3 hierarchy**: 46
- **Milestone denominator (excluding `multicall`)**: 45
- **Currently importable on `main` (`10f697bbb`)**: **32 / 45 (71.11%)** (32 / 46 = 69.57% including `multicall`)
- **Importable with open PR `#2515` (`feat/solidity-import-interface-static-call`)**: **33 / 45 (73.33%)** (unlocks `isHealthy(Market,bytes32,address)`)

### 32 Functions Importable on `main` (`10f697bbb`)
1. `setConfigurator(address)`
2. `setFeeSetter(address)`
3. `setFeeClaimer(address)`
4. `setTickSpacingSetter(address)`
5. `enableLltv(uint256)`
6. `enableLiquidationCursor(uint256)`
7. `setMarketTickSpacing(bytes32,uint256)`
8. `setMarketSettlementFee(bytes32,uint256,uint256)`
9. `setDefaultSettlementFee(address,uint256,uint256)`
10. `setMarketContinuousFee(bytes32,uint256)`
11. `setDefaultContinuousFee(address,uint256)`
12. `setConsumed(bytes32,uint128,address)`
13. `setIsAuthorized(address,bool,address)`
14. `updatePositionView(Market,bytes32,address)`
15. `_updatePosition(Market,bytes32,address)`
16. `settlementFee(bytes32,uint256)`
17. `hasCredit(bytes32,address)`
18. `credit(bytes32,address)`
19. `pendingFee(bytes32,address)`
20. `lastLossFactor(bytes32,address)`
21. `lastAccrual(bytes32,address)`
22. `debt(bytes32,address)`
23. `collateralBitmap(bytes32,address)`
24. `collateral(bytes32,address,uint256)`
25. `totalUnits(bytes32)`
26. `lossFactor(bytes32)`
27. `withdrawable(bytes32)`
28. `continuousFeeCredit(bytes32)`
29. `settlementFeeCbps(bytes32)`
30. `continuousFee(bytes32)`
31. `tickSpacing(bytes32)`
32. `liquidationLocked(bytes32,address)`

---

## 2. Recently Merged `solidity_import` PRs on `main`

| PR | Commit | Merged At | Summary |
| --- | --- | --- | --- |
| `#2503` | `10f697bbb` | 2026-10-12T00:14:25Z | Support calldata slices, Governor proposer description checks, `bytes1..bytes31` locals/casts, and `MemberAccess` tuple assignments (Slice 42) |
| `#2502` | `f40a74f20` | 2026-10-11T20:38:13Z | Support `Create2`/`Clones` Yul address prediction, `keccak256(_msgData())`, and bounded deque pop `while` loops (Slice 41) |
| `#2501` | `5fd3b744b` | 2026-10-11T16:30:20Z | Support `ECDSA` Yul signature unpacking, `StorageSlot` raw string/bytes slots, and error scalar casts (Slice 40) |
| `#2500` | `78503ccd1` | 2026-10-11T14:42:09Z | Support `Strings.toHexString`, `Arrays.findUpperBound`, `BitMaps.setTo`, and decrementing `for` loops (Slice 39) |
| `#2499` | `e32d3e632` | 2026-10-11T12:20:13Z | Support string/bytes mappings, `Strings` formatting, and `ERC721URIStorage` (Slice 38) |
| `#2498` | `eeec8df8f` | 2026-10-11T10:16:25Z | Support `TimelockController` operation hashing/scheduling, `bytes4` literal casts, and constant error helpers (Slice 37) |
| `#2497` | `033a3f05f` | 2026-10-11T08:57:45Z | Support fixed-array struct getters and storage-key member writes (Slice 36) |
| `#2496` | `5a340eb5b` | 2026-10-11T05:05:33Z | Support Yul memory-struct `keccak256` and flat-struct member compound/inc-dec ops (Slice 35) |
| `#2495` | `78494fd53` | 2026-10-11T03:08:14Z | Support `EcrecoverAuthorizer`, `Arrays`, and `EnumerableMap` patterns (Slice 34) |
| `#2494` | `d26f6390d` | 2026-10-11T00:52:30Z | Support public state variable getters and builtin revert/remappings (Slice 33) |
| `#2493` | `1075f477e` | 2026-10-10T22:23:42Z | Support function-pointer helper params and root flat-struct returns (Slice 32) |
| `#2492` | `aee9a65ad` | 2026-10-10T19:31:37Z | Support `abi.decode` and Merkle ratifier patterns (Slice 31) |
| `#2491` | `203a1788f` | 2026-10-10T16:50:45Z | Support nested dynamic ABI structs, bytes fields, and `Offer` EIP-712 hashing (Slice 30) |
| `#2490` | `68ea41fd5` | 2026-10-10T13:53:28Z | Support `TickLib` `wExp`/`priceToTick`, 3-key mappings, and top-level fixed storage arrays (Slice 29) |
| `#2489` | `9e6c93c96` | 2026-10-10T10:53:10Z | Support `Checkpoints`, struct storage arrays, named struct constructors, and binary-search `while` loops (Slice 28) |
| `#2488` | `4a0621c21` | 2026-10-10T07:40:33Z | Support dynamic storage arrays, `Arrays.unsafeAccess`, and `EnumerableSet`/`EnumerableMap` (Slice 27) |
| `#2487` | `69412678a` | 2026-10-10T03:02:12Z | Support ERC-7201 raw-slot storage structs, `StorageSlot` string/bytes, and `ShortStrings.toString` (Slice 26) |

---

## 3. Open PRs (`#2504`–`#2516`) and Rescue/Feature Branches Inventory

### Open PRs

| PR | Branch | Head SHA | Base | Status | Relationship / Overlap | Next Step |
| --- | --- | --- | --- | --- | --- | --- |
| `#2504` | `feat/solidity-import-create2-parent-gas-linux` | `18a6f9af9` | `main` | Open (Draft) | Foundation for `#2505` (CREATE2 execution derived from parent gas and byte memory + `InitCodeExecution` + `BytesObjectMemory`). | Active on `old-agent` (`938bba18`): verify exact-head merge gates and merge with merge commit. |
| `#2505` | `feat/solidity-import-account-storage-bridge-linux` | `ce0f194e4` | `feat/solidity-import-create2-parent-gas-linux` | Open (Draft) | Stacked on `#2504`. Synchronizes persistent flat writes with finite account storage (`AccountStorageBridge`). | Active on `old-agent` (`938bba18`): finish `Compiler/Proofs/IRGeneration/GenericInduction/Storage.lean` via persistent REPL daemon, run full merge gates, and merge. |
| `#2506` | `fix/ci-main-green` | `1c0913470` | `main` | Open (Ready) | Shards `scripts/solidity_import_mutations.py` (`--shard`, `--jobs`) into a 6-way CI matrix job (`import-mutations`). | Verify exact-head local merge gates and merge. |
| `#2507` | `feat/solidity-import-contractstate-byte-memory` | `51992ad76` | `main` | Open (Draft) | Shares base commits `49a7b9cc7..4321b29eb` with `#2508`. Contains `58c9774b4` (dirty-worktree dump) plus `51992ad76` (`NativeSourceElementFreePointer.lean`). | Fold `NativeSourceElementFreePointer.lean` (`51992ad76`) into `#2508`, then close `#2507` with a link once merged. |
| `#2508` | `feat/solidity-import-byte-call-physical` | `ac92387cd` | `main` | Open (Draft) | Clean physical byte memory carrier (`ContractState.byteMemory`) + closed byte external-call boundary (`ByteExternalCall`, `DenoteByteExternalCalls`, `SolidityStaticCall.uint256Module`, `Stmt.revertEmpty`). Supersedes `rescue/verity-import-byte-call-boundary-20261017`. | Active on `sepolia` (`2b9a4c4f`): finish `FunctionBody/Stmt.lean` physical `mstore` proof using `scripts/lean_repl_daemon.py`, fold `rescue/verity-proofs-20261017` (`18a0c739e`) + `#2507` (`51992ad76`), run full merge gates, and merge. |
| `#2509` | `feat/solidity-import-slice-43` | `0dd5e5def` | `main` | Open (Draft) | Solidity 0.8.10 and `AccessManagerTargetRoleSequence` importer work (`Import.lean`, `AbiLowering.lean`, `AccessManagerTargetRoleSequence.sol`). | Rebase on `main`, complete per-family checklist and exact-head merge gates, and merge. |
| `#2510` | `wip/solidity-import-tuples` | `35c1dd9d4` | `main` (conflicting, merge-base `9d0d56a67`) | Open (Draft, Conflicting) | Contains `ConstantSequence`, `ArithmeticSequence`, `MemberWriteSequence`, `LoopSequence`, `UncheckedSequence`, and `TupleSequence` fixtures/mutations/variants plus tuple assignment lowering in `Import.lean`. | Rebase onto current `main`, resolve conflicts keeping all sequence fixtures/mutations and unique `Import.lean` tuple improvements from both sides, run full merge gates, and merge. |
| `#2511` | `recovered/verity-translation-dispatcher` | `7c839dc36` | `main` (merge-base `6e275b4d3`) | Open (Draft) | Extends `experiments/solidity-translation-validation` with `MemoryGuardExtension.lean`, `DispatcherDecoder.lean`, `DispatcherExecution.lean`, and `DispatcherNodes.lean`. Supersedes `rescue/verity-solidity-import-20261017`. | Rebase onto current `main`, verify all translation-validation scripts and full merge gates, and merge. |
| `#2512` | `proof/solidity-import-adversarial-sequences` | `3b5355392` | `main` | Open (Draft) | Adds `Compiler/SolidityImport/AdversarialEntryPointInvariants.lean` proving invariant preservation across per-call adversarial oracle choices. | Verify full exact-head merge gates and merge. |
| `#2513` | `fix/solidity-differential-head-identity` | `6c5b8abc3` | `main` | Open (Draft) | Rejects Git HEAD commit switches during stateful differential replay (`scripts/solidity_differential/identity.py`). | Verify full exact-head merge gates and merge. |
| `#2514` | `test/solidity-import-midnight-stateful` | `d65d930cb` | `main` | Open (Draft) | Stateful multi-entry-point differential harness. Currently uses Midnight-specific naming (`check_midnight_admin.py`, `docs/MIDNIGHT_STATEFUL.md`) and top-level `eth_abi` import. | Refactor in Track M2 into a generic multi-entrypoint stateful differential runner (with lazy `eth_abi`/`eth_utils` imports), run full merge gates, and merge. |
| `#2515` | `feat/solidity-import-interface-static-call` | `8b803cd65` | `main` | Open (Draft) | Lowers typed-interface `uint256` view staticcalls (`I(addr).f()`) onto `#2508`'s closed byte transport. Unlocks Midnight `isHealthy` (**33/45 = 73.33%**). | Rebase on merged `#2508` (folding `rescue/verity-proofs-20261017`), finish the 9-mutant `check_interface_static_call_mutations.py` run and full merge gates, and merge. |
| `#2516` | `docs/agents-repl-mathlib-guide` | `4156c5e7a` | `main` | Open (Ready) | Restores `AGENTS.md`, syncs `CLAUDE.md`, and adds persistent Unix-socket Lean REPL daemon (`scripts/lean_repl_daemon.py` + `scripts/test_lean_repl_daemon.py`), Mathlib4 code style rules, generic-construct rules, and proof abstraction guidelines. | Run full merge gates and merge onto `main`. |

### Named Rescue and Feature Branches

| Branch | Head SHA | Status & Disposition |
| --- | --- | --- |
| `rescue/verity-import-byte-call-boundary-20261017` | `494a4b2d8` | Fully contained in and superseded by `#2508` (`feat/solidity-import-byte-call-physical`). |
| `rescue/verity-solidity-import-20261017` | `94edef54a` | Pre-`#2451` rescue of `experiments/solidity-translation-validation`; superseded by `main` + `#2511`. |
| `rescue/verity-proofs-20261017` | `18a0c739e` | Continuation of `#2515` + `#2508` repairing `DenoteAgreement.lean` and `EvmYulLeanCallClosure.lean`. Fold `18a0c739e` into `#2508` / `#2515`. |
| `feat/solidity-import-byte-call-physical` | `ac92387cd` | Tracked by open PR `#2508`. |
| `feat/solidity-import-interface-static-call` | `8b803cd65` | Tracked by open PR `#2515`. |

---

## 4. Scheduled Refactor Campaign (Midnight Decoupling + Mathlib4 Style & Abstractions)

1. **Track M1 — Decouple Midnight Specifics from Importer, Stdlib, Proofs & Coverage (`refactor/decouple-midnight-core`)** — **ACTIVE on `ashur` (`8ebd2cbf`)**:
   - Remove hardcoded `fname == "popFront" || fname == "popBack"` and `_begin`/`_end` field checks in `Compiler/SolidityImport/Import.lean` (`isDequePopCall?`), and remove `m0Name == "value"` in raw-slot string/bytes struct wrapper recognition in favor of structural AST checks.
   - Rename `enoughForMidnightRcfTotalUnits` → `TransitionSummary.isNonEmpty` in `Compiler/Proofs/GeneratedTransition.lean` and `GeneratedTransitionTest.lean`.
   - Move Midnight-specific tick constants (`WEXP_TICK_LN_ONE_PLUS_DELTA`, `WEXP_MAX_TICK_HALF`, `WEXP_PRICE_ROUNDING_STEP`, `tickToPriceReference`) out of `Verity/Stdlib/Math.lean`.
   - Replace hardcoded `if project['id'] == 'midnight':` in `scripts/solidity_import_coverage.py` with a generic optional `"exclude_functions"` field in `scripts/solidity_import_corpus/manifest.json`.
2. **Track M2 — Replace `pinned-midnight`, `MarketAbi`, `MidnightPositionAndFeeSequence` & PR `#2514` with Construct-Generic Fixtures (`refactor/decouple-midnight-fixtures`)** — **QUEUED NEXT**:
   - Replace `Contracts/SolidityImportSmoke/pinned-midnight/` and `MarketAbi.sol` with generic multi-file nested dynamic struct ABI fixtures (`NestedDynamicStructAbi.sol`, `check_nested_dynamic_struct_abi.py`).
   - Rename `MidnightPositionAndFeeSequence` → `PackedStructMappingAndTernaryTupleSequence` with generic domain-free struct/function names.
   - Rework PR `#2514` (`test/solidity-import-midnight-stateful`) into a generic multi-entrypoint stateful differential harness (`check_stateful_admin.py` with lazy `eth_abi`/`eth_utils` imports).
3. **Track S1 — Mathlib4 Code Style, Naming & Compositional State/Frame Lenses (`refactor/mathlib-style-and-frame-lenses`)** — **SCHEDULED**:
   - Enforce Mathlib4 conventions across `Compiler/Proofs/` and `Compiler/SolidityImport/`: `UpperCamelCase` types/Props, `lowerCamelCase` defs/terms, descriptive `snake_case` theorems/lemmas (`_of_`, `_iff`, `_eq`, `_ne`, `_lt`, `_le`), structured `· ` focusing dots, `<100` chars/line, `<30` lines/proof.
   - Introduce reusable `@[simp]` frame/lens combinators for `ContractState` updates (`storage`, `transientStorage`, `memory`, `byteMemory`, `returndata`, `events`) and `irreducible` / step-equation barriers so proofs compose without unfolding giant interpreter definitions.
4. **Track S2 — Modular File Decomposition & Heartbeat Reduction (`refactor/modular-split-and-heartbeat-reduction`)** — **SCHEDULED**:
   - Split monolithic files (`Compiler/SolidityImport/Import.lean`, `Compiler/Proofs/IRGeneration/FunctionBody/Stmt.lean`, `Compiler/Proofs/IRGeneration/SourceSemantics.lean`) by construct family / semantic layer with minimal `import` cones to speed up parallel `lake build` and REPL header loading.
   - Eliminate `set_option maxHeartbeats` escalations by replacing unconstrained `simp` with `simp only` / `rw` and extracting `<30`-line helper lemmas.

---

## 5. Ordered Remaining Construct Families (All Implemented Generically, Prioritized by Corpus Histogram: 33/45 → 45/45)

1. **Family A — Generic Yul `create2(v, ptr, len, salt)` Byte-Payload Deployment & Struct Event Emission (`emit Event(Struct, bytes32 indexed)`)**:
   - Unlocks 2 functions immediately (**35 / 45 = 77.78%**) and unblocks 9 total.
2. **Family B — External Code Size (`<addr>.code.length` / `extcodesize`) & Low-Level `.call` with Optional-Bool Returndata Decode**:
   - Unlocks 5 additional functions (**40 / 45 = 88.89%**).
3. **Family C — External Runtime Code Read (`<addr>.code`) & Dynamic Struct `abi.decode` with Root Struct Return**:
   - Unlocks 1 function (**41 / 45 = 91.11%**).
4. **Family D — Typed-Interface View Staticcalls Returning `bool` and `bytes32` (with Dynamic Struct/Bytes Args)**:
   - Unblocks gate and ratifier staticcalls.
5. **Family E — Typed-Interface State-Changing External Callbacks Returning `bytes32` & Dynamic/Signed Event Emissions**:
   - Unlocks remaining 4 functions (**45 / 45 = 100.00%**).

---

## 6. Active Subagent Missions

| Track | Machine (`node_id`) | Mission ID | Backend / Model | Target PRs / Branches | Status |
| --- | --- | --- | --- | --- | --- |
| `refactor-decouple-midnight-core-v2` | `ashur` | `8ebd2cbf-7610-4abc-8404-cda470f0ddf3` | `claudecode` / `claude-opus-5-5` (`high`) | `refactor/decouple-midnight-core` (Track M1: `Import.lean`, `GeneratedTransition.lean`, `Verity/Stdlib/Math.lean`, `solidity_import_coverage.py`) | Running (`AGENTS.md` + `lean_repl_daemon.py` installed; refactoring `isDequePopCall?`, raw-slot wrapper, `Math.lean`, and coverage manifest) |
| `adopt-sepolia-repl-v1` | `sepolia` | `2b9a4c4f-00d3-4ab1-b450-f15d78417cf5` | `claudecode` / `claude-opus-5-5` (`high`) | `#2508` (`feat/solidity-import-byte-call-physical`) + `rescue/verity-proofs-20261017` (`18a0c739e`) + `#2507` (`51992ad76`) | Running (adopted `1dbb43b3` worktree on `sepolia` with 1-process enforcement, installed `AGENTS.md` + `scripts/lean_repl_daemon.py`, finishing `Stmt.lean` physical `mstore` proof) |
| `adopt-worker-repl-v1` | `old-agent` | `938bba18-dd96-4ea9-9133-f72bbbd3f15b` | `claudecode` / `claude-opus-5-5` (`high`) | `#2504` (`feat/solidity-import-create2-parent-gas-linux`) + `#2505` (`feat/solidity-import-account-storage-bridge-linux`) | Running (adopted `64aa91b8` worktree on `old-agent` with 1-process enforcement, installed `AGENTS.md` + `scripts/lean_repl_daemon.py`, finishing `#2504` gates & `#2505` `Storage.lean` proofs) |


