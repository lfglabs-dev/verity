# Uniswap v4 (`v4-core`) Model Support

Verity's Solidity importer (`Compiler/SolidityImport/Import.lean` + `Compiler/SolidityImport/InlineAssemblyShims.lean`) last measured support (#2694) for **35 of 38 probes** on Uniswap v4's `PoolManager.sol` (`Uniswap/v4-core` commit `3779387e5ef296f39df54cd2bb1dca9a6eff46f8`, `solc 0.8.26`, Cancun EVM, `viaIR := true`). This is a historical baseline, not a measurement after the negated-loop rejection and selector-revert shim removal.

## 1. Modular Inline-Assembly Shim Architecture (`InlineAssemblyShims.lean`)

To keep `Compiler/SolidityImport/Import.lean` modular and verifiable, Uniswap v4 inline-assembly (`Yul`) idioms and low-level helper patterns are encapsulated in [`Compiler/SolidityImport/InlineAssemblyShims.lean`](../Compiler/SolidityImport/InlineAssemblyShims.lean) and lowered to closed `CompilationModel` statements, expressions, and `ExternalCallModule` (ECM) primitives:

| Verified Compiler Shim | Library / Contract | `VerifiedCompilerShimKind` | Lowered `CompilationModel` Representation |
| --- | --- | --- | --- |
| `Exttload.exttload(bytes32)` | `Exttload` | `.exttloadSingle` | Scratch `mstore(0, tload(slot))` + `.returnValues [.mload (.literal 0)]` |
| `Exttload.exttload(bytes32[])` | `Exttload` | `.exttloadBatch` | `lowerBatchArrayLoadShim` (`Stmt.forEach` + `Expr.tload` + `Stmt.returnBytes`) |
| `Extsload.extsload(bytes32)` | `Extsload` | `.extsloadSingle` | Scratch `mstore(0, sload(slot))` + `.returnValues [.mload (.literal 0)]` |
| `Extsload.extsload(bytes32,uint256)` | `Extsload` | `.extsloadRange` | `lowerBatchRangeSloadShim` (`Stmt.forEach` + `Expr.storageArrayElement` + `Stmt.returnBytes`) |
| `Extsload.extsload(bytes32[])` | `Extsload` | `.extsloadBatch` | `lowerBatchArrayLoadShim` (`Stmt.forEach` + `Expr.storageArrayElement` + `Stmt.returnBytes`) |
| `CurrencyLibrary.transfer` | `CurrencyLibrary` | `.currencyTransfer` | `lowerCurrencyTransferShim` (`SolidityLowLevelCall.bytesBoolModule` + `.require`) |
| `FullMath.mulDiv` | `FullMath` | `.fullMathMulDiv` | `Expr.mulDivDown` / `Expr.mulDivUp` + inline Yul arithmetic lowering |
| `BitMath.mostSignificantBit` | `BitMath` | `.bitMathMsb` | Branchless `shr` / `gt` Yul statement lowering (`lowerYulStmtSlice`) |
| `BitMath.leastSignificantBit` | `BitMath` | `.bitMathLsb` | De Bruijn / branchless bit scan lowering (`lowerYulStmtSlice`) |
| `TickMath.getSqrtPriceAtTick` / `getTickAtSqrtPrice` | `TickMath` | `.tickMath` | Inline Yul bit/shift/comparison lowering (`YulLiteral` booleans, `signextend`, `sar`, `shl`, `shr`) |
| `TickBitmap.flipTick` | `TickBitmap` | `.tickBitmapFlip` | `lowerTickBitmapFlipShim` (`sdiv`/`smod` word-pos & bit-pos + `sload`/`sstore` XOR mask) |
| `Hooks.callHook` | `Hooks` | `.hooksCall` | `lowerHooksCallShim` (`SolidityLowLevelCall.bytesUint256Module` + selector/delta extraction) |

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
5. **Dynamic `bytes` Arguments in `abi.encodeCall` (`Hooks.callHook`)**:
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
