# Solidity Import Campaign Status (`coord/status`)

Last updated: 2026-10-17T10:08:00Z
Coordinator mission: `300051ac-f398-4e6b-b2da-412dbc470673` (replaces `ebb2f1fe`)
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

## 3. Open PRs (`#2504`–`#2515`) and Rescue/Feature Branches Inventory

### Open PRs

| PR | Branch | Head SHA | Base | Status | Relationship / Overlap | Next Step |
| --- | --- | --- | --- | --- | --- | --- |
| `#2504` | `feat/solidity-import-create2-parent-gas-linux` | `18a6f9af9` | `main` | Open (Draft) | Foundation for `#2505` (CREATE2 execution derived from parent gas and byte memory + `InitCodeExecution` + `BytesObjectMemory`). | Rebase/integrate with `#2508` physical memory, run full exact-head gates (`make check`, mutations, smoke/loss/programs, `PrintAxioms`, Midnight pilot), and merge with merge commit. |
| `#2505` | `feat/solidity-import-account-storage-bridge-linux` | `ce0f194e4` | `feat/solidity-import-create2-parent-gas-linux` | Open (Draft) | Stacked on `#2504`. Synchronizes persistent flat writes with finite account storage (`AccountStorageBridge`). Fails `GenericInduction/Storage.lean` until physical-slot write lemmas are updated. | Rebase on `#2504` + `#2508`, fix `Compiler/Proofs/IRGeneration/GenericInduction/Storage.lean` for `writePhysicalSlot`/`writePhysicalMap`/`writePhysicalMap2`, run full merge gates, and merge. |
| `#2506` | `fix/ci-main-green` | `1c0913470` | `main` | Open (Ready) | Shards `scripts/solidity_import_mutations.py` (`--shard`, `--jobs`) into a 6-way CI matrix job (`import-mutations`) so `build` stays well under 120m. | Verify exact-head local merge gates (`make check`, mutations, smoke/loss/programs, `PrintAxioms`, Midnight pilot) and merge first among CI/instrument PRs. |
| `#2507` | `feat/solidity-import-contractstate-byte-memory` | `51992ad76` | `main` | Open (Draft) | Shares base commits `49a7b9cc7..4321b29eb` with `#2508`. Contains `58c9774b4` (broad dirty-worktree rescue dump of 949 files including `PROGRESS.md`) plus `51992ad76` (`NativeSourceElementFreePointer.lean`). | Fold `NativeSourceElementFreePointer.lean` (`51992ad76`) and any unique validated proof/test modules from `#2507` into `#2508` (or a clean follow-up proof PR without `PROGRESS.md`), then close `#2507` with a link once its content is merged. |
| `#2508` | `feat/solidity-import-byte-call-physical` | `ac92387cd` | `main` | Open (Draft) | Clean physical byte memory carrier (`ContractState.byteMemory`) + closed byte external-call boundary (`ByteExternalCall`, `DenoteByteExternalCalls`, `SolidityStaticCall.uint256Module`, `Stmt.revertEmpty`) + physical ABI/Panic/`Error(string)` proof repairs. Supersedes `rescue/verity-import-byte-call-boundary-20261017`. | Fold `DenoteAgreement.lean` and `EvmYulLeanCallClosure.lean` repairs from `rescue/verity-proofs-20261017` (`18a0c739e`), finish `Compiler/Proofs/IRGeneration/FunctionBody/Stmt.lean` physical `mstore` proof migration, fold `51992ad76` (`NativeSourceElementFreePointer.lean`) from `#2507`, run full merge gates, and merge first (dependency root). |
| `#2509` | `feat/solidity-import-slice-43` | `0dd5e5def` | `main` | Open (Draft) | Solidity 0.8.10 and `AccessManagerTargetRoleSequence` importer work (`Import.lean`, `AbiLowering.lean`, `AccessManagerTargetRoleSequence.sol`). | Rebase on `main`, complete per-family checklist and exact-head merge gates, and merge. |
| `#2510` | `wip/solidity-import-tuples` | `35c1dd9d4` | `main` (conflicting, merge-base `9d0d56a67`) | Open (Draft, Conflicting) | Contains `ConstantSequence`, `ArithmeticSequence`, `MemberWriteSequence`, `LoopSequence`, `UncheckedSequence`, and `TupleSequence` fixtures/mutations/variants plus tuple assignment lowering in `Import.lean`. | Rebase onto current `main`, resolve conflicts keeping all sequence fixtures/mutations and any unique `Import.lean` tuple improvements from both sides, run full merge gates, and merge. |
| `#2511` | `recovered/verity-translation-dispatcher` | `7c839dc36` | `main` (merge-base `6e275b4d3`) | Open (Draft) | Extends `experiments/solidity-translation-validation` with `MemoryGuardExtension.lean`, `DispatcherDecoder.lean`, `DispatcherExecution.lean`, and `DispatcherNodes.lean`. Supersedes `rescue/verity-solidity-import-20261017`. | Rebase onto current `main`, verify all translation-validation scripts and full merge gates, and merge. |
| `#2512` | `proof/solidity-import-adversarial-sequences` | `3b5355392` | `main` | Open (Draft) | Adds `Compiler/SolidityImport/AdversarialEntryPointInvariants.lean` proving invariant preservation across per-call adversarial oracle choices. | Verify full exact-head merge gates and merge. |
| `#2513` | `fix/solidity-differential-head-identity` | `6c5b8abc3` | `main` | Open (Draft) | Rejects Git HEAD commit switches during stateful differential replay (`scripts/solidity_differential/identity.py`). | Verify full exact-head merge gates and merge. |
| `#2514` | `test/solidity-import-midnight-stateful` | `d65d930cb` | `main` | Open (Draft) | Adds `scripts/solidity_differential/check_midnight_admin.py` exercising 10 pinned Midnight entry points across 256 stateful A/B/C transactions. Fails `make check` in CI when `eth_abi` is absent from the system unittest environment. | Guard/lazy-load `eth_abi`/`eth_utils` imports for unit tests (`scripts/test_midnight_stateful_inputs.py`) so `make check` passes without external venv packages, run full merge gates, and merge. |
| `#2515` | `feat/solidity-import-interface-static-call` | `8b803cd65` | `main` | Open (Draft) | Lowers typed-interface `uint256` view staticcalls (`I(addr).f()`) onto `#2508`'s closed byte transport. Unlocks Midnight `isHealthy` (**33/45 = 73.33%**). | Rebase on merged `#2508` (folding `rescue/verity-proofs-20261017`), finish the 9-mutant `check_interface_static_call_mutations.py` run and full merge gates, and merge. |

### Named Rescue and Feature Branches

| Branch | Head SHA | Status & Disposition |
| --- | --- | --- |
| `rescue/verity-import-byte-call-boundary-20261017` | `494a4b2d8` | Fully contained in and superseded by `#2508` (`feat/solidity-import-byte-call-physical`), which integrates physical byte memory and `execByteExternalCall` on top of all 16 files from this rescue commit. |
| `rescue/verity-solidity-import-20261017` | `94edef54a` | Pre-`#2451` rescue of `experiments/solidity-translation-validation` (20/22 files identical to `main`; remaining 2 files have newer revisions on `main` and in `#2511` `recovered/verity-translation-dispatcher`). Superseded by `main` + `#2511`. |
| `rescue/verity-proofs-20261017` | `18a0c739e` | Continuation of `#2515` (`feat/solidity-import-interface-static-call`) + `#2508` (`de48c1d10`) with commit `18a0c739e` repairing `Compiler/Proofs/IRGeneration/DenoteAgreement.lean` and `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanCallClosure.lean`. Fold `18a0c739e` into `#2508` / `#2515`. |
| `feat/solidity-import-byte-call-physical` | `ac92387cd` | Tracked by open PR `#2508` (see above). |
| `feat/solidity-import-interface-static-call` | `8b803cd65` | Tracked by open PR `#2515` (see above). |

### Step 1b Dependency Merge Order for Open PRs
1. **Wave 1 (Foundations, Proofs, and CI/Harness Instruments)**:
   - `#2506` (`fix/ci-main-green`) — mutation sharding and runner fixes
   - `#2513` (`fix/solidity-differential-head-identity`) — stateful replay Git HEAD check
   - `#2512` (`proof/solidity-import-adversarial-sequences`) — per-call adversarial oracle invariant proofs
   - `#2508` (`feat/solidity-import-byte-call-physical` + `rescue/verity-proofs-20261017` `18a0c739e` + `#2507` `51992ad76`) — physical byte memory & byte external-call boundary
2. **Wave 2 (CREATE2 Account World, Interface Staticcall, Midnight Stateful, Rescue Branches)**:
   - `#2504` (`feat/solidity-import-create2-parent-gas-linux`) & `#2505` (`feat/solidity-import-account-storage-bridge-linux`) — CREATE2 parent gas, byte memory initcode execution, and finite account storage bridge
   - `#2515` (`feat/solidity-import-interface-static-call` + `rescue/verity-proofs-20261017`) — typed-interface `uint256` view staticcalls (brings Midnight coverage to **33/45 = 73.33%**)
   - `#2514` (`test/solidity-import-midnight-stateful`) — stateful Midnight 10-entry-point differential harness
   - `#2509` (`feat/solidity-import-slice-43`), `#2510` (`wip/solidity-import-tuples`), `#2511` (`recovered/verity-translation-dispatcher`)

---

## 4. Ordered Remaining Construct Families for Midnight (33/45 → 45/45)

Ordered by the Midnight coverage histogram (most Midnight functions unlocked or advanced first):

1. **Family A — SSTORE2 `create2` Deployment (`IdLib.storeInCode`) & Struct Event Emission (`EventsLib.MarketCreated(Market, bytes32 indexed)`)**:
   - **Source locations**: `src/libraries/IdLib.sol:40:28` (`create2Address := create2(0, add(creationCode, 0x20), mload(creationCode), 0)` on `abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))`) and `src/Midnight.sol:784:18` (`emit EventsLib.MarketCreated(market, id)`).
   - **Histogram impact**: First blocker for **9 functions** (`touchMarket`, `updatePosition`, `claimContinuousFee`, `withdraw`, `withdrawCollateral`, `supplyCollateral`, `repay`, `liquidate`, `take`).
   - **Immediate unlocks**: `touchMarket(Market)` and `updatePosition(Market,address)` → **35 / 45 (77.78%)**.

2. **Family B — External Code Size (`token.code.length`) & ERC-20 Low-Level Call with Optional-Bool Decode (`SafeTransferLib.safeTransfer` / `safeTransferFrom`)**:
   - **Source locations**: `src/libraries/SafeTransferLib.sol:13:17` (`token.code.length > 0` → `extcodesize`), `SafeTransferLib.sol:15:46` / `26:46` (`(bool success, bytes memory returndata) = token.call(abi.encodeCall(IERC20.transfer / transferFrom, ...))`), `SafeTransferLib.sol:17-19` (`revert(add(returndata, 0x20), mload(returndata))`), and `SafeTransferLib.sol:21` (`returndata.length == 0 || abi.decode(returndata, (bool))`).
   - **Histogram impact**: Reached by **9 functions** (`claimSettlementFee`, `claimContinuousFee`, `withdraw`, `withdrawCollateral`, `supplyCollateral`, `repay`, `flashLoan`, `liquidate`, `take`).
   - **Immediate unlocks** (after `#2515` + Family A): `claimSettlementFee`, `claimContinuousFee`, `withdraw`, `withdrawCollateral`, `supplyCollateral` → **40 / 45 (88.89%)**.

3. **Family C — External Runtime Code Read (`<addr>.code`) & Dynamic Struct `abi.decode(..., (Market))` with Root Struct Return (`toMarket`)**:
   - **Source locations**: `src/Midnight.sol:902:16` (`return abi.decode(create2Address.code, (Market))` reading SSTORE2 payload after 1-byte `0x00` stop prefix or full runtime code per `IdLib.SSTORE2_PREFIX` which deploys `abi.encode(market)` directly as runtime code).
   - **Immediate unlocks**: `toMarket(bytes32)` → **41 / 45 (91.11%)**.

4. **Family D — Typed-Interface View Staticcalls Returning `bool` (`IEnterGate`, `ILiquidatorGate`) and `bytes32` (`IRatifier.isRatified`)**:
   - **Source locations**:
     - `src/Midnight.sol:591:51`: `ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)` (`address -> view returns (bool)`)
     - `src/Midnight.sol:385:20`, `390:20`: `IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)` / `canIncreaseDebt(seller)` (`address -> view returns (bool)`)
     - `src/Midnight.sol:343:17`: `IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)` (`(Offer, bytes, address) -> view returns (bytes32)`)
   - **Histogram impact**: Unblocks gate and ratifier checks in `liquidate` and `take`.

5. **Family E — Typed-Interface State-Changing Callbacks Returning `bytes32` (`onRepay`, `onFlashLoan`, `onLiquidate`, `onBuy`, `onSell`) & Dynamic/Signed Event Emissions (`FlashLoan`, `Take`)**:
   - **Source locations**:
     - `src/Midnight.sol:508:17`: `IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)` → unlocks `repay` (**42 / 45 = 93.33%**)
     - `src/Midnight.sol:735:14` (`emit EventsLib.FlashLoan(msg.sender, tokens, assets, callback)`) + `740:13` (`IFlashLoanCallback(callback).onFlashLoan(...)`) → unlocks `flashLoan` (**43 / 45 = 95.56%**)
     - `src/Midnight.sol:694:17`: `ILiquidateCallback(callback).onLiquidate(...)` → unlocks `liquidate` (**44 / 45 = 97.78%**)
     - `src/Midnight.sol:414:14` (`emit EventsLib.Take(...)` with `bytes ratifierData` and `int256`) + `440:17` (`IBuyCallback.onBuy`) + `453:17` (`ISellCallback.onSell`) → unlocks `take` (**45 / 45 = 100.00%**)

---

## 5. Active Subagent Missions

*(To be updated as subagents are launched)*
