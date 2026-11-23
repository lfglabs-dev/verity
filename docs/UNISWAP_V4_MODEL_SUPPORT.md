# Uniswap v4 (`v4-core`) Model Support

Verity's Solidity importer (`Compiler/SolidityImport/Import.lean` + `Compiler/SolidityImport/InlineAssemblyShims.lean`) last measured support (#2694) for **35 of 38 probes** on Uniswap v4's `PoolManager.sol` (`Uniswap/v4-core` commit `3779387e5ef296f39df54cd2bb1dca9a6eff46f8`, `solc 0.8.26`, Cancun EVM, `viaIR := true`). This is a historical baseline, not a measurement after the negated-loop rejection and selector-revert shim removal. Since #2847 a closed low-level CALL must be the last state interaction of its function. `CurrencyLibrary.transfer` is no longer replaced by a CALL shortcut: its body is lowered like any other library function (see below), which changes how `take` and `collectProtocolFees`, which reach it, import. `TickBitmap.flipTick` is no longer replaced by a bitmap shortcut either (see below). `Hooks.callHook` is no longer replaced by a CALL shortcut: its body is lowered like any other helper and rejected at its first `assembly` block (`src/libraries/Hooks.sol:133:9` at `v4-core` `46c6834`, the commit pinned in `scripts/solidity_import_corpus/manifest.json`), so `initialize`, `donate`, `modifyLiquidity` and `swap`, which reach it, are expected to reject there. This has not been re-measured.

## 1. Trusted shortcuts (`InlineAssemblyShims.lean`)

Three `v4-core` inline-assembly blocks are not translated: [`Compiler/SolidityImport/InlineAssemblyShims.lean`](../Compiler/SolidityImport/InlineAssemblyShims.lean) registers them in `trustedImporterShortcuts`, each with the fingerprint of the exact block, the fixed lowering that replaces it and the tests that back it. These shortcuts are trusted, not verified: no Lean proof relates a lowering to its block (see "Trusted shortcuts" in [`docs/SOLIDITY_IMPORT.md`](SOLIDITY_IMPORT.md#trust-boundary)).

| Block (`v4-core` `46c6834`) | Fingerprint constant | `TrustedShortcutLowering` | Fixed lowering |
| --- | --- | --- | --- |
| `Exttload.exttload(bytes32[])` | `exttloadBatchYulFingerprint` | `.batchTransientRead` | `lowerBatchArrayLoadShim` (`Stmt.forEach` + `Expr.tload` + `SolidityReturnMemory`) |
| `Extsload.extsload(bytes32,uint256)` | `extsloadRangeYulFingerprint` | `.rangeStorageRead` | `lowerBatchRangeSloadShim` (`Stmt.forEach` + `Expr.storageArrayElement` + `SolidityReturnMemory`) |
| `Extsload.extsload(bytes32[])` | `extsloadBatchYulFingerprint` | `.batchStorageRead` | `lowerBatchArrayLoadShim` (`Stmt.forEach` + `Expr.storageArrayElement` + `SolidityReturnMemory`) |

Every other `v4-core` function, including the single-slot `exttload` / `extsload`, `FullMath`, `BitMath`, `TickMath`, `SqrtPriceMath`, `SwapMath`, `Pool.updateTick` and `unlockCallback`, has no shortcut: it is lowered through the ordinary Solidity and Yul lowering, or rejected. The former registry `uniswapV4VerifiedShims` listed 15 "verified" entries whose flags were set by hand; 12 of them selected no lowering. It and its theorems were removed (#2828).

`lowerBatchArrayLoadShim` is applied only to a tail `assembly` block whose `yulBlockFingerprint` (sha256 of its solc Yul AST without source positions) is `extsloadBatchYulFingerprint` or `exttloadBatchYulFingerprint`, taken from `v4-core` `46c6834`, and whose Solidity references all resolve to the bound calldata array. Any other tail block of a `bytes32[]`-returning function that references the one array bound in scope is rejected with `shortcut fingerprint mismatch`; a tail block that does not reference it takes the ordinary assembly lowering (`Contracts/SolidityImportSmoke/TailAssemblyArrayReadChecks.lean`). Both rules hold whatever the contract's state-variable count (formerly only with more than one state variable; `Contracts/SolidityImportSmoke/RootArrayReturnStateCountChecks.lean`, #2830).

`lowerBatchRangeSloadShim` is applied only to a tail `assembly` block whose `yulBlockFingerprint` is `extsloadRangeYulFingerprint` (same `v4-core` commit) and whose Yul identifiers `startSlot` and `nSlots` resolve, through `externalReferences`, to one unshadowed `bytes32` and one `uint256` variable, and the block references no other declaration (`rangeReadBindings?`). It used to apply whenever Solidity variables with those two names were in scope. Any other block takes the ordinary assembly lowering (`Contracts/SolidityImportSmoke/TailAssemblyRangeReadChecks.lean`). The fingerprint selects the block; it does not by itself show that the lowering agrees with it.

`Hooks.callHook` has no shortcut: a helper of that name is lowered through its own body like any other helper (`Contracts/SolidityImportSmoke/BytesHelperNameIndependenceChecks.lean`). It used to be replaced by a fixed low-level CALL (`lowerHooksCallShim`, removed) whenever a two-argument string/bytes helper was named `callHook`, whatever its body. v4's body has a named `bytes memory` result and inline assembly, which the ordinary helper lowering does not admit (it rejects at the first `assembly` block, the CALL), so `initialize`, `donate`, `modifyLiquidity` and `swap` cannot import through it.

`CurrencyLibrary.transfer` has no shortcut: a three-argument `transfer` of a library named `CurrencyLibrary` is lowered through its own body like any other library function (`Contracts/SolidityImportSmoke/LibraryHelperNameIndependenceChecks.lean`). It used to be replaced by a fixed native-value or ERC-20 `transfer` CALL with an empty revert (`lowerCurrencyTransferShim`, removed) whatever its body, in a contract with more than one state variable. The ordinary Yul lowering admits a `call` only when its value argument is the literal 0. v4's body passes `amount` as the value of its native-value `call` (`src/types/Currency.sol:48:44` at `v4-core` `46c6834`), so `take` and `collectProtocolFees`, which reach it, are expected to reject at that site or earlier. This is a prediction from a simplified fixture (`address` instead of the `Currency` type, `== address(0)` instead of `isAddressZero()`), not a measurement.

`TickBitmap.flipTick` has no shortcut: a three-argument `flipTick` of a library named `TickBitmap` is lowered through its own body like any other library function (`Contracts/SolidityImportSmoke/MappingLibraryNameIndependenceChecks.lean`). It used to be replaced by a fixed bitmap XOR with an empty misalignment revert (`lowerTickBitmapFlipShim`, removed) whatever its body, in a contract with more than one state variable; v4's own body reverts with `TickMisaligned(tick, tickSpacing)` data instead. v4's body reads the free-memory pointer to build that revert payload (`src/libraries/TickBitmap.sol:58:28` at `v4-core` `46c6834`), which the ordinary Yul lowering admits only to restore the pointer or place a bubbled revert. Only `Pool.modifyLiquidity` calls it, so only the `modifyLiquidity` probe can be affected. Measured: the last coverage run (#2694, `v4-core` `3779387`) rejected that probe at `LiquidityMath.sol:16:17`, a site that may no longer reject. Predicted, not re-measured: the probe still rejects, so the probe count does not change, because `PoolManager.modifyLiquidity` reaches `Hooks.callHook` (through `beforeModifyLiquidity`, `src/PoolManager.sol:156` at `46c6834`) before `pool.modifyLiquidity`, and that body is rejected (see above).

## 2. General Importer Enhancements Supporting `v4-core`

Alongside the trusted shortcuts in `InlineAssemblyShims.lean`, `Compiler/SolidityImport/Import.lean`, `StorageLayout.lean`, `Coverage.lean`, and `Quote.lean` support:

1. **Signed Mapping Keys & Signed Struct Members in `StorageLayout.lean`**:
   - Decodes `mapping(int24 => TickInfo) ticks` and `mapping(int16 => uint256) tickBitmap` in `Pool.State` as `.uint256` word keys and `int128 liquidityNet` as packed signed struct members.
2. **Storage Mapping Reference Forwarding (`mapping(...) storage`)**:
   - `lowerRef`, `lowerCallArgs`, and `bindHelperParams` propagate `mapping(...) storage` references (`self.ticks`, `self.tickBitmap`) as `.rawSlot` storage paths across internal library helper calls (`TickBitmap.flipTick`, `TickBitmap.nextInitializedTickWithinOneWord`, `Pool.clearTick`).
3. **Internal Storage-Struct Pointer Root Parameters & Returns (`_getPool`)**:
   - `bindRoot` and `lowerRootStatements` lower internal functions taking or returning `Pool.State storage` as raw base-slot `uint256` words without shadowing `SPath.rawSlot` in `env.values`.
4. **Conditional Placeholder Modifiers (`Hooks.noSelfCall`)**:
   - On entry points, lowered by substitution since #2846 (the body runs only when `msg.sender != address(this)`); on internal helpers, rejected at the modifier (`only a single top-level _; placeholder is supported in modifiers`) whatever the state-variable count (#2830). With more than one state variable, `lowerModifier` used to lower `if (msg.sender != address(this)) _;` to a no-op `if` after the body, which only `inlineVoidFn` turned into a conditional around a void helper body; roots and value helpers ran the body unconditionally. Every v4 function using `noSelfCall` also reaches `Hooks.callHook`, which already rejects (see above), so no probe that imported depended on it. Not re-measured.
5. **Dynamic `bytes` Arguments in `abi.encodeCall` (the hook calldata built for `Hooks.callHook`)**:
   - `lowerEncodedBytes` encodes `abi.encodeCall(IHooks.beforeInitialize, (...))` and dynamic `bytes calldata hookData` arguments using `AbiEncoding.Spec` (`AbiEncoding.Field.word` + `AbiEncoding.Field.bytes`).
6. **`msg.value` Support in `Coverage.lean` and `Quote.lean`**:
   - `exprCovered` covers `Expr.msgValue` (`evalExpr_msgValue_arm`), and `Quote.lean` quotes `Expr.msgValue`.

## 3. `PoolManager.sol` Function Inventory (historical baseline)

In the last measured run (#2694), every probed function below except `modifyLiquidity` and `swap` elaborated via `solidity_import` with `modelImportCovered model = true`. The `35/38` count is over the coverage tool's 38 probes, which differ from this table: they also probe `_swap`, `_burn`, `checkNotDelegateCall` and `_updateProtocolFees` (only `_swap` rejected there, at the same site as `swap`), and they do not probe rows 19, 20, 24, 25, 27, 28 and 29:

| # | Function Signature | Category |
| --- | --- | --- |
| 1 | `unlock(bytes)` | Core Lock / Callback (`IUnlockCallback.unlockCallback`) |
| 2 | `initialize(PoolKey, uint160)` | Pool Lifecycle + Hooks (`beforeInitialize`, `afterInitialize`) |
| 3 | `modifyLiquidity(PoolKey, ModifyLiquidityParams, bytes)` | **Rejected in the last coverage run** at `src/libraries/LiquidityMath.sol:16:17`. That scratch-memory revert now fits `Stmt.revertMemory`; the first diagnostic has not been re-measured. `Position.calculatePositionKey` also uses `mload(0x40)` at `src/libraries/Position.sol:55:24`. That helper previously imported through a name-keyed shim that hashed `abi.encode` of four words (128 bytes) instead of the helper's 58-byte packed key. |
| 4 | `swap(PoolKey, SwapParams, bytes)` | **Rejected in the last coverage run** at `src/libraries/SqrtPriceMath.sol:200:21`, as was `_swap`. That selector revert now fits `Stmt.revertMemory`, but both paths reach the negated step-loop condition in `Pool.swap` (`src/libraries/Pool.sol`). The importer rejects that condition before lowering the loop body rather than silently stopping after 256 iterations. The first diagnostic on these entry points has not been re-measured. |
| 5 | `donate(PoolKey, uint256, uint256, bytes)` | Pool Donation + Hooks |
| 6 | `sync(Currency)` | Transient Reserve Sync (`Reserves.setSyncedReserves`) |
| 7 | `take(Currency, address, uint256)` | Currency Accounting + `CurrencyLibrary.transfer` |
| 8 | `settle()` | Native Currency Settlement (`msg.value` + `_settle`) |
| 9 | `settleFor(address)` | Delegated Settlement (`_settle`) |
| 10 | `clear(Currency, uint256)` | Exact Balance Delta Clearing (`NonzeroNativeValue`, `MustClearExactPositiveDelta`) |
| 11 | `mint(address, uint256, uint256)` | ERC-6909 Claims Mint + `CurrencyDelta.applyDelta` |
| 12 | `burn(address, uint256, uint256)` | ERC-6909 Claims Burn + `CurrencyDelta.applyDelta` |
| 13 | `updateDynamicLPFee(PoolKey, uint24)` | Dynamic LP Fee Update (`onlyValidCaller` hook check) |
| 14 | `_settle(address)` | Internal Settlement Helper (`CurrencyLibrary.balanceOfSelf`) |
| 15 | `_accountDelta(Currency, int128, address)` | Internal Transient Delta Accounting (`NonzeroDeltaCount`) |
| 16 | `_accountPoolBalanceDelta(PoolKey, BalanceDelta, address)` | Internal Two-Currency Delta Accounting |
| 17 | `_getPool(PoolId)` | Internal `Pool.State storage` Base-Slot Lookup |
| 18 | `_isUnlocked()` | Internal `Lock.isUnlocked()` View |
| 19 | `protocolFeesAccrued(Currency)` | `ProtocolFees` Public Getter |
| 20 | `protocolFeeController()` | `ProtocolFees` Public Getter |
| 21 | `setProtocolFeeController(address)` | `ProtocolFees` Setter (`onlyOwner`) |
| 22 | `setProtocolFee(PoolKey, uint24)` | `ProtocolFees` Pool Update |
| 23 | `collectProtocolFees(address, Currency, uint256)` | `ProtocolFees` Collection + `CurrencyLibrary.transfer` |
| 24 | `_fetchProtocolFee(PoolKey)` | `ProtocolFees` Internal `IProtocolFeeController` Call (`try/catch` / low-level call) |
| 25 | `owner()` | `Owned` Public Getter |
| 26 | `transferOwnership(address)` | `Owned` Ownership Transfer (`onlyOwner`) |
| 27 | `balanceOf(address, uint256)` | `ERC6909` Public Getter |
| 28 | `allowance(address, address, uint256)` | `ERC6909` Public Getter |
| 29 | `isOperator(address, address)` | `ERC6909` Public Getter |
| 30 | `transfer(address, uint256, uint256)` | `ERC6909` Transfer |
| 31 | `transferFrom(address, address, uint256, uint256)` | `ERC6909` Delegated Transfer |
| 32 | `approve(address, uint256, uint256)` | `ERC6909` Approval |
| 33 | `setOperator(address, bool)` | `ERC6909` Operator Update |
| 34 | `supportsInterface(bytes4)` | `ERC6909` ERC-165 Introspection |
| 35 | `_mint(address, uint256, uint256)` | `ERC6909Claims` Internal Mint |
| 36 | `_burnFrom(address, uint256, uint256)` | `ERC6909Claims` Internal Burn |
| 37 | `extsload(bytes32)` | `Extsload` Single-Slot Storage Introspection |
| 38 | `extsload(bytes32, uint256)` | `Extsload` Contiguous-Range Storage Introspection |
| 39* | `extsload(bytes32[])` | `Extsload` Batch-Array Storage Introspection |
| 40* | `exttload(bytes32)` | `Exttload` Single-Slot Transient Introspection |
| 41* | `exttload(bytes32[])` | `Exttload` Batch-Array Transient Introspection |

*(The count includes distinct overloads: `extsload` has three and `exttload` has two.)*

Revert helpers now inline through their bodies. A nonempty literal range below `0x40` lowers to `Stmt.revertMemory` when the same Yul block wrote every byte on every path. The body determines whether a selector revert returns four bytes or a selector plus a 32-byte argument; the error declaration does not. Helpers that use `mload(0x40)` to allocate a wrapped error, including `CustomRevert.bubbleUpAndRevertWith`, reject at the unsupported assembly rather than importing as empty reverts.
