# Solidity Import Campaign Status (`coord/status`)

Last updated: 2026-10-17T18:45:00Z
Coordinator mission: `34056738-029f-4b19-b400-7fbd99593784` (replaces `795c3c1d` / `608d2555` / `aae68584` / `300051ac` / `ebb2f1fe`)
Current `main` HEAD: `846121b85` (`#2513`)

---

## 1. Pinned Midnight Coverage Summary (`src/Midnight.sol` @ `96d31343e993329e7a593dde46516a2c0cbcd142`)

- **Total implemented functions in `Midnight` C3 hierarchy**: 46
- **Milestone denominator (excluding `multicall` via manifest `exclude_functions`)**: 45
- **Currently importable on `main` (`846121b85`)**: **32 / 45 (71.11%)** (32 / 46 = 69.57% including `multicall`)
- **Importable with open PR `#2515` (`feat/solidity-import-interface-static-call`)**: **33 / 45 (73.33%)** (unlocks `isHealthy(Market,bytes32,address)`)

### 32 Functions Importable on `main` (`846121b85`)
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
| `#2513` | `846121b85` | 2026-10-17T18:43:15Z | Reject Git HEAD commit switches during stateful differential replay (`scripts/solidity_differential/identity.py`) |
| `#2505` | `94414bd6e` | 2026-10-17T18:39:59Z | Synchronize persistent flat writes with finite account storage (`AccountStorageBridge`, physical-slot frame/storage lenses) |
| `#2504` | `b219c4d01` | 2026-10-17T18:39:08Z | Derive CREATE2 execution from parent gas and byte memory (`Create2ParentGas`, `Create2Opcode`, `InitCodeExecution`, `BytesObjectMemory`, `DenoteCreate2`) |
| `#2517` | `0c4d56c49` | 2026-10-17T17:10:40Z | Decouple Midnight/OZ identifiers from importer (`isBoundedRangePopCall?`, `isStorageStructBytesMember`), `GeneratedTransition.lean`, `Verity/Stdlib/Math.lean`, and `solidity_import_coverage.py` (Track M1) |
| `#2506` | `2de2bf80a` | 2026-10-17T17:08:50Z | Shard importer mutation campaigns out of the proof build job (`--shard`, `--jobs auto`, `--task`) and fix 22 broken mutation anchors on `main` |
| `#2516` | `ce39baf83` | 2026-10-17T17:07:24Z | Add `AGENTS.md`/`CLAUDE.md` REPL, Mathlib4 style & generic construct guide + persistent Unix-socket Lean REPL daemon (`scripts/lean_repl_daemon.py`) |
| `#2503` | `10f697bbb` | 2026-10-12T00:14:25Z | Support calldata slices, Governor proposer description checks, `bytes1..bytes31` locals/casts, and `MemberAccess` tuple assignments (Slice 42) |
| `#2502` | `f40a74f20` | 2026-10-11T20:38:13Z | Support `Create2`/`Clones` Yul address prediction, `keccak256(_msgData())`, and bounded deque pop `while` loops (Slice 41) |
| `#2501` | `5fd3b744b` | 2026-10-11T16:30:20Z | Support `ECDSA` Yul signature unpacking, `StorageSlot` raw string/bytes slots, and error scalar casts (Slice 40) |
| `#2500` | `78503ccd1` | 2026-10-11T14:42:09Z | Support `Strings.toHexString`, `Arrays.findUpperBound`, `BitMaps.setTo`, and decrementing `for` loops (Slice 39) |
| `#2499` | `e32d3e632` | 2026-10-11T12:20:13Z | Support string/bytes mappings, `Strings` formatting, and `ERC721URIStorage` (Slice 38) |
| `#2498` | `eeec8df8f` | 2026-10-11T10:16:25Z | Support `TimelockController` operation hashing/scheduling, `bytes4` literal casts, and constant error helpers (Slice 37) |
| `#2497` | `033a3f05f` | 2026-10-11T08:57:45Z | Support fixed-array struct getters and storage-key member writes (Slice 36) |

---

## 3. Open PRs (`#2507`–`#2515`) and Rescue/Feature Branches Inventory

### Open PRs

| PR | Branch | Head SHA | Base | Status | Relationship / Overlap | Next Step |
| --- | --- | --- | --- | --- | --- | --- |
| `#2507` | `feat/solidity-import-contractstate-byte-memory` | `51992ad76` | `main` | Open (Superseded) | Folded into `#2508` (`3250227f2`). | Close `#2507` with a link once `#2508` merges. |
| `#2508` | `feat/solidity-import-byte-call-physical` | `3250227f2` | `main` | Open | Physical byte memory carrier (`ContractState.byteMemory`) + closed byte external-call boundary (`ByteExternalCall`, `DenoteByteExternalCalls`, `SolidityStaticCall.uint256Module`, `Stmt.revertEmpty`). Unused-var warnings fixed at `3250227f2`. | Active on `sepolia` (`18f11242`): merge `origin/main` (`846121b85`), run `byte-call` and `import-bare-empty-revert` mutation tasks + gates, push, and merge. |
| `#2509` | `feat/solidity-import-slice-43` | `0dd5e5def` | `main` | Open | Solidity 0.8.10 and `AccessManagerTargetRoleSequence` importer work (`Import.lean`, `AbiLowering.lean`, `AccessManagerTargetRoleSequence.sol`). | Active on `ashur` (`522e12b1`): merge `origin/main`, complete per-family checklist and exact-head merge gates, and merge. |
| `#2510` | `wip/solidity-import-tuples` | `35c1dd9d4` | `main` (conflicting) | Open (Conflicting) | Contains `ConstantSequence`, `ArithmeticSequence`, `MemberWriteSequence`, `LoopSequence`, `UncheckedSequence`, and `TupleSequence` fixtures/mutations/variants plus tuple assignment lowering in `Import.lean`. | Active on `ashur` (`522e12b1`): cherry-pick/rebase unmerged commits onto `origin/main`, run full merge gates, and merge. |
| `#2511` | `recovered/verity-translation-dispatcher` | `7c839dc36` | `main` | Open | Extends `experiments/solidity-translation-validation` with `MemoryGuardExtension.lean`, `DispatcherDecoder.lean`, `DispatcherExecution.lean`, and `DispatcherNodes.lean`. Supersedes `rescue/verity-solidity-import-20261017`. | Active on `ashur` (`522e12b1`): merge `origin/main`, verify translation-validation scripts and full merge gates, and merge. |
| `#2512` | `proof/solidity-import-adversarial-sequences` | `3b5355392` | `main` | Open | Adds `Compiler/SolidityImport/AdversarialEntryPointInvariants.lean` proving invariant preservation across per-call adversarial oracle choices. | Active on `ashur` (`522e12b1`): merge `origin/main`, verify merge gates, and merge. |
| `#2514` | `test/solidity-import-midnight-stateful` | `d65d930cb` | `main` | Open | Stateful multi-entry-point differential harness. Currently uses Midnight-specific naming (`check_midnight_admin.py`, `docs/MIDNIGHT_STATEFUL.md`). | Active on `old-agent` (`d4031c0b`) as part of Track M2 (`refactor/decouple-midnight-fixtures`): fold generic multi-entrypoint harness into `verity` without Midnight-specific files, then close `#2514` with link. |
| `#2515` | `feat/solidity-import-interface-static-call` | `8b803cd65` | `main` | Open | Lowers typed-interface `uint256` view staticcalls (`I(addr).f()`) onto `#2508`'s closed byte transport. Unlocks Midnight `isHealthy` (**33/45 = 73.33%**). | Active on `sepolia` (`18f11242`): merge updated `#2508`, run `check_interface_static_call_mutations.py` and merge gates, and merge. |

### Named Rescue and Feature Branches

| Branch | Head SHA | Status & Disposition |
| --- | --- | --- |
| `rescue/verity-import-byte-call-boundary-20261017` | `494a4b2d8` | Fully contained in and superseded by `#2508` (`feat/solidity-import-byte-call-physical`). |
| `rescue/verity-solidity-import-20261017` | `94edef54a` | Pre-`#2451` rescue of `experiments/solidity-translation-validation`; superseded by `main` + `#2511`. |
| `rescue/verity-proofs-20261017` | `18a0c739e` | Folded into `#2508` (`3250227f2`). |
| `feat/solidity-import-byte-call-physical` | `3250227f2` | Tracked by open PR `#2508`. |
| `feat/solidity-import-interface-static-call` | `8b803cd65` | Tracked by open PR `#2515`. |

---

## 4. Scheduled Refactor Campaign (Midnight Decoupling + Mathlib4 Style & Abstractions)

1. **Track M1 — Decouple Midnight Specifics from Importer, Stdlib, Proofs & Coverage (`refactor/decouple-midnight-core`)** — **MERGED (`#2517`, `0c4d56c49`)**.
2. **Track M2 — Replace `pinned-midnight`, `MarketAbi`, `MidnightPositionAndFeeSequence` & PR `#2514` with Construct-Generic Fixtures (`refactor/decouple-midnight-fixtures`)** — **ACTIVE on `old-agent` (`d4031c0b`)**:
   - Replace `Contracts/SolidityImportSmoke/pinned-midnight/` and `MarketAbi.sol` with generic multi-file nested dynamic struct ABI fixtures (`NestedDynamicStructAbi.sol`, `check_nested_dynamic_struct_abi.py`).
   - Rename `MidnightPositionAndFeeSequence` → `PackedStructMappingAndTernaryTupleSequence` with generic domain-free struct/function names.
   - Rework PR `#2514` (`test/solidity-import-midnight-stateful`) into a generic multi-entrypoint stateful differential harness.
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

## 6. Active Subagent Missions (Strictly 1 Subagent per Worker Node)

| Track | Machine (`node_id`) | Mission ID | Backend / Model | Target PRs / Branches | Status |
| --- | --- | --- | --- | --- | --- |
| `refactor-decouple-midnight-fixtures-v1` | `old-agent` | `d4031c0b-f2c2-42b4-87c3-4f56e417ba5f` | `claudecode` / `claude-opus-5-5` (`high`) | `refactor/decouple-midnight-fixtures` (Track M2: genericize `pinned-midnight`, `MarketAbi`, `MidnightPositionAndFeeSequence`, and `#2514`) | Active (committed `c9fd6b43a`, running final 2 packed-struct mutation tasks) |
| `pr-2508-physical-byte-memory` | `sepolia` | `18f11242-fb29-4184-bc66-0e211ef86aad` | `claudecode` / `claude-opus-5-5` (`high`) | `#2508` (`feat/solidity-import-byte-call-physical`) + `#2515` (`feat/solidity-import-interface-static-call`) | Active |
| `pr-2512-2509-2511-step1b-v1` | `ashur` | `522e12b1-9c7f-4879-bda2-f679720d9780` | `claudecode` / `claude-opus-5-5` (`high`) | `#2512` (`proof/solidity-import-adversarial-sequences`) + `#2511` (`recovered/verity-translation-dispatcher`) + `#2509` (`feat/solidity-import-slice-43`) + `#2510` (`wip/solidity-import-tuples`) | Active |



