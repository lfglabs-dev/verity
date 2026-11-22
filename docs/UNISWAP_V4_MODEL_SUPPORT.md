# Uniswap v4 (`v4-core`) Model Support

Verity's Solidity importer (`Compiler/SolidityImport/Import.lean` + `Compiler/SolidityImport/InlineAssemblyShims.lean`) last measured support (#2694) for **35 of 38 probes** on Uniswap v4's `PoolManager.sol` (`Uniswap/v4-core` commit `3779387e5ef296f39df54cd2bb1dca9a6eff46f8`, `solc 0.8.26`, Cancun EVM, `viaIR := true`). This is a historical baseline, not a measurement after the negated-loop rejection and selector-revert shim removal. Since #2847 a closed low-level CALL must be the last state interaction of its function. `CurrencyLibrary.transfer` is no longer replaced by a CALL shortcut: its body is lowered like any other library function (see below), which changes how `take` and `collectProtocolFees`, which reach it, import. `TickBitmap.flipTick` is no longer replaced by a bitmap shortcut either (see below). `Hooks.callHook` is no longer replaced by a CALL shortcut: its body is lowered like any other helper and rejected at its first `assembly` block (`src/libraries/Hooks.sol:133:9` at `v4-core` `46c6834`, the commit pinned in `scripts/solidity_import_corpus/manifest.json`), so `initialize`, `donate`, `modifyLiquidity` and `swap`, which reach it, are expected to reject there. This has not been re-measured.

## 1. Modular Inline-Assembly Shim Architecture (`InlineAssemblyShims.lean`)

To keep `Compiler/SolidityImport/Import.lean` modular and verifiable, Uniswap v4 inline-assembly (`Yul`) idioms and low-level helper patterns are encapsulated in [`Compiler/SolidityImport/InlineAssemblyShims.lean`](../Compiler/SolidityImport/InlineAssemblyShims.lean) and lowered to closed `CompilationModel` statements, expressions, and `ExternalCallModule` (ECM) primitives:

| Verified Compiler Shim | Library / Contract | `VerifiedCompilerShimKind` | Lowered `CompilationModel` Representation |
| --- | --- | --- | --- |
| `Exttload.exttload(bytes32)` | `Exttload` | `.exttloadSingle` | Scratch `mstore(0, tload(slot))` + `.returnValues [.mload (.literal 0)]` |
| `Exttload.exttload(bytes32[])` | `Exttload` | `.exttloadBatch` | `lowerBatchArrayLoadShim` (`Stmt.forEach` + `Expr.tload` + `Stmt.returnBytes`) |
| `Extsload.extsload(bytes32)` | `Extsload` | `.extsloadSingle` | Scratch `mstore(0, sload(slot))` + `.returnValues [.mload (.literal 0)]` |
| `Extsload.extsload(bytes32,uint256)` | `Extsload` | `.extsloadRange` | `lowerBatchRangeSloadShim` (`Stmt.forEach` + `Expr.storageArrayElement` + `Stmt.returnBytes`) |
| `Extsload.extsload(bytes32[])` | `Extsload` | `.extsloadBatch` | `lowerBatchArrayLoadShim` (`Stmt.forEach` + `Expr.storageArrayElement` + `Stmt.returnBytes`) |
| `FullMath.mulDiv` | `FullMath` | `.fullMathMulDiv` | `Expr.mulDivDown` / `Expr.mulDivUp` + inline Yul arithmetic lowering |
| `BitMath.mostSignificantBit` | `BitMath` | `.bitMathMsb` | Branchless `shr` / `gt` Yul statement lowering (`lowerYulStmtSlice`) |
| `BitMath.leastSignificantBit` | `BitMath` | `.bitMathLsb` | De Bruijn / branchless bit scan lowering (`lowerYulStmtSlice`) |
| `TickMath.getSqrtPriceAtTick` / `getTickAtSqrtPrice` | `TickMath` | `.tickMath` | Inline Yul bit/shift/comparison lowering (`YulLiteral` booleans, `signextend`, `sar`, `shl`, `shr`) |

`lowerBatchArrayLoadShim` is applied only to a tail `assembly` block whose `yulBlockFingerprint` (sha256 of its solc Yul AST without source positions) is `extsloadBatchYulFingerprint` or `exttloadBatchYulFingerprint`, taken from `v4-core` `46c6834`, and whose Solidity references all resolve to the bound calldata array. Any other tail block of a `bytes32[]`-returning function with one array parameter is rejected with `shortcut fingerprint mismatch` (`Contracts/SolidityImportSmoke/TailAssemblyArrayReadChecks.lean`). Both rules hold whatever the contract's state-variable count (formerly only with more than one state variable; `Contracts/SolidityImportSmoke/RootArrayReturnStateCountChecks.lean`, #2830).

`lowerBatchRangeSloadShim` is applied only to a tail `assembly` block whose `yulBlockFingerprint` is `extsloadRangeYulFingerprint` (same `v4-core` commit) and whose Yul identifiers `startSlot` and `nSlots` resolve, through `externalReferences`, to one unshadowed `bytes32` and one `uint256` variable, and the block references no other declaration (`rangeReadBindings?`). It used to apply whenever Solidity variables with those two names were in scope. Any other block takes the ordinary assembly lowering (`Contracts/SolidityImportSmoke/TailAssemblyRangeReadChecks.lean`). The fingerprint selects the block; it does not by itself show that the lowering agrees with it.

`Hooks.callHook` has no shortcut: a helper of that name is lowered through its own body like any other helper (`Contracts/SolidityImportSmoke/BytesHelperNameIndependenceChecks.lean`). It used to be replaced by a fixed low-level CALL (`lowerHooksCallShim`, removed) whenever a two-argument string/bytes helper was named `callHook`, whatever its body. v4's body has a named `bytes memory` result and inline assembly, which the ordinary helper lowering does not admit (it rejects at the first `assembly` block, the CALL), so `initialize`, `donate`, `modifyLiquidity` and `swap` cannot import through it. The `.hooksCall` entry of `uniswapV4VerifiedShims` is left for the registry work of #2828; the importer does not consult it.

`CurrencyLibrary.transfer` has no shortcut: a three-argument `transfer` of a library named `CurrencyLibrary` is lowered through its own body like any other library function (`Contracts/SolidityImportSmoke/LibraryHelperNameIndependenceChecks.lean`). It used to be replaced by a fixed native-value or ERC-20 `transfer` CALL with an empty revert (`lowerCurrencyTransferShim`, removed) whatever its body, in a contract with more than one state variable. The ordinary Yul lowering admits a `call` only when its value argument is the literal 0. v4's body passes `amount` as the value of its native-value `call` (`src/types/Currency.sol:48:44` at `v4-core` `46c6834`), so `take` and `collectProtocolFees`, which reach it, are expected to reject at that site or earlier. This is a prediction from a simplified fixture (`address` instead of the `Currency` type, `== address(0)` instead of `isAddressZero()`), not a measurement. The `.currencyTransfer` entry of `uniswapV4VerifiedShims` is left for the registry work of #2828; the importer does not consult it and its flags are not backed by any lowering.

`TickBitmap.flipTick` has no shortcut: a three-argument `flipTick` of a library named `TickBitmap` is lowered through its own body like any other library function (`Contracts/SolidityImportSmoke/MappingLibraryNameIndependenceChecks.lean`). It used to be replaced by a fixed bitmap XOR with an empty misalignment revert (`lowerTickBitmapFlipShim`, removed) whatever its body, in a contract with more than one state variable; v4's own body reverts with `TickMisaligned(tick, tickSpacing)` data instead. v4's body reads the free-memory pointer to build that revert payload (`src/libraries/TickBitmap.sol:58:28` at `v4-core` `46c6834`), which the ordinary Yul lowering admits only to restore the pointer or place a bubbled revert. Only `Pool.modifyLiquidity` calls it, so only the `modifyLiquidity` probe can be affected. Measured: the last coverage run (#2694, `v4-core` `3779387`) rejected that probe at `LiquidityMath.sol:16:17`, a site that may no longer reject. Predicted, not re-measured: the probe still rejects, so the probe count does not change, because `PoolManager.modifyLiquidity` reaches `Hooks.callHook` (through `beforeModifyLiquidity`, `src/PoolManager.sol:156` at `46c6834`) before `pool.modifyLiquidity`, and that body is rejected (see above). The `.tickBitmapFlip` entry of `uniswapV4VerifiedShims` is left for the registry work of #2828; the importer does not consult it and its flags are not backed by any lowering.

### 3-Layer Meta-Specification Bundle

`Compiler/SolidityImport/InlineAssemblyShims.lean` exports a 3-layer specification bundle:
- **Layer I (`InlineAssemblyShimsMetaSpec`)**: Conjunction of `allShimsVerified = true` and `uniswapV4VerifiedShims.length = 15`, proved in `inlineAssemblyShims_satisfies_metaSpec`.
- **Layer II (`uniswapV4VerifiedShims_all_verified`, `uniswapV4VerifiedShims_length`)**: 1–3 line projection corollaries derived from Layer I.
- **Layer III (`witness_findVerifiedShim_exttloadSingle`, `witness_findVerifiedShim_fullMathMulDiv`, `witness_findVerifiedShim_unlockCallback`)**: Concrete `by decide` witnesses.

## 2. General Importer Enhancements Supporting `v4-core`

Alongside the shims in `InlineAssemblyShims.lean`, `Compiler/SolidityImport/Import.lean`, `StorageLayout.lean`, `Coverage.lean`, and `Quote.lean` support:

1. **Signed Mapping Keys & Signed Struct Members in `StorageLayout.lean`**:
   - Decodes `mapping(int24 => TickInfo) ticks` and `mapping(int16 => uint256) tickBitmap` in `Pool.State` as `.uint256` word keys and `int128 liquidityNet` as packed signed struct members.
2. **Storage Mapping Reference Forwarding (`mapping(...) storage`)**:
   - `lowerRef`, `lowerCallArgs`, and `bindHelperParams` propagate `mapping(...) storage` references (`self.ticks`, `self.tickBitmap`) as `.rawSlot` storage paths across internal library helper calls (`TickBitmap.flipTick`, `TickBitmap.nextInitializedTickWithinOneWord`, `Pool.clearTick`).
3. **Internal Storage-Struct Pointer Root Parameters & Returns (`_getPool`)**:
   - `bindRoot` and `lowerRootStatements` lower internal functions taking or returning `Pool.State storage` as raw base-slot `uint256` words without shadowing `SPath.rawSlot` in `env.values`.
4. **Conditional Placeholder Modifiers (`Hooks.noSelfCall`)**:
   - `lowerModifier` and `inlineVoidFn` lower `modifier noSelfCall() { if (msg.sender != address(this)) _; }` into a conditional statement wrapping the modified helper body.
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
