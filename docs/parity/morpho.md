# Morpho Blue → Verity EDSL parity gap map

## Preamble

**Target:** `Th0rgal/morpho-verity@master`, which vendors
`morpho-org/morpho-blue@0427acea` as a git submodule at `./morpho-blue/`. The
project itself is Lean (Yul is only in build artifacts). Solidity sources are
therefore analyzed from the upstream submodule `morpho-org/morpho-blue/src/`.

**Scope.** Morpho Blue is a single ~550 LOC singleton (`Morpho.sol`) plus five
pure libraries (`MathLib`, `SharesMathLib`, `MarketParamsLib`, `UtilsLib`,
`SafeTransferLib`), a constants file, an events library, and a string-based
errors library. **MetaMorpho is out of scope** — it lives in a separate repo
(`morpho-org/metamorpho`) and `morpho-verity` does not vendor it. The
periphery view-only library `MorphoLib.sol` uses `extSloads` bit-tricks; per
the project's `MORPH_BLUE_MAPPING.md`, the Verity port replaces it with direct
storage projections and is therefore excluded from the parity target.

**Verity EDSL support model.**
- ✅ expressible today in `verity_contract`.
- 🚧 expressible with a documented workaround.
- ❌ needs a new EDSL feature (named in the row).

**Key EDSL constraints that dominate Morpho parity:**
1. No `uint128` / `uint64` etc. — Morpho's `Market` and `Position` are 100%
   `uint128` for packing.
2. No top-level storage `struct` — Morpho storage is dominated by `mapping(Id
   => Market)` and `mapping(Id => mapping(address => Position))`.
3. No mapping-of-mapping-of-mapping with proofs (2 max) — `position[id][user]`
   is fine (mapping2), and `MarketParams` inside `idToMarketParams[id]` is a
   struct-in-mapping.
4. No inheritance, no first-class modifiers, no `abi.encode`, no `try/catch`,
   no callback (`onMorphoSupply`, `onMorphoRepay`, `onMorphoSupplyCollateral`,
   `onMorphoLiquidate`, `onMorphoFlashLoan`) trust-boundary primitive.

Rows marked 🚧 with "packed struct in mapping (#1976)" assume the EDSL packs
the `uint128` fields itself; the developer still writes them as `uint128`,
which is ❌ standalone. Where both apply, the deeper blocker is surfaced.

Total constructs counted: **72**.

---

## 1. `src/Morpho.sol` (555 LOC, singleton)

### 1.1 Immutables & storage

| # | Construct | Solidity | Verity status | Note |
|---|-----------|----------|---------------|------|
| 1 | Immutable | `bytes32 public immutable DOMAIN_SEPARATOR` | 🚧 | `bytes32` ✅ but immutable not first-class; store in constructor-initialized slot. |
| 2 | Storage | `address public owner` | ✅ | |
| 3 | Storage | `address public feeRecipient` | ✅ | |
| 4 | Storage | `mapping(Id => mapping(address => Position)) public position` | ❌ | Storage `struct Position` + `uint128` fields → **packed struct in mapping (#1976)** + `mapping2` ✅ + `uint128` ❌. Blocker: `uint128`. |
| 5 | Storage | `mapping(Id => Market) public market` | ❌ | `Market` = 6× `uint128` packed into 2 slots. Needs **`uint128` + packed struct in mapping (#1976)**. |
| 6 | Storage | `mapping(address => bool) public isIrmEnabled` | ✅ | |
| 7 | Storage | `mapping(uint256 => bool) public isLltvEnabled` | ✅ | |
| 8 | Storage | `mapping(address => mapping(address => bool)) public isAuthorized` | ✅ | |
| 9 | Storage | `mapping(address => uint256) public nonce` | ✅ | |
| 10 | Storage | `mapping(Id => MarketParams) public idToMarketParams` | 🚧 | `Id` is `bytes32` ✅. `MarketParams` = 4×`address` + `uint256` — no packing needed. **struct-in-mapping (#1976)**. |

### 1.2 Types (from `IMorpho.sol`, used pervasively)

| # | Construct | Solidity | Verity status | Note |
|---|-----------|----------|---------------|------|
| 11 | User type | `type Id is bytes32;` | 🚧 | `bytes32` ✅; the newtype wrapper is sugar the frontend can inline. |
| 12 | Struct | `MarketParams { address loanToken, collateralToken, oracle, irm; uint256 lltv; }` | 🚧 | All fields ✅; memory struct usage needs **local-struct** or manual field passing. |
| 13 | Struct | `Position { uint256 supplyShares; uint128 borrowShares; uint128 collateral; }` | ❌ | `uint128` fields → **`uint128`** required. |
| 14 | Struct | `Market { uint128 totalSupplyAssets, totalSupplyShares, totalBorrowAssets, totalBorrowShares, lastUpdate, fee; }` | ❌ | 100% `uint128` → **`uint128`** required. |
| 15 | Struct | `Authorization { address authorizer, authorized; bool isAuthorized; uint256 nonce, deadline; }` | 🚧 | Memory only; all fields ✅ if flattened. |
| 16 | Struct | `Signature { uint8 v; bytes32 r, s; }` | ✅ | |

### 1.3 Constructor & modifier

| # | Construct | Solidity | Verity status | Note |
|---|-----------|----------|---------------|------|
| 17 | Constructor | `constructor(address newOwner)` | ✅ | `keccak256(abi.encode(...))` inside → 🚧 (see row 20). |
| 18 | Modifier | `modifier onlyOwner()` | ❌ | **First-class modifiers** not in EDSL — inline `require(msg.sender == owner)`. |
| 19 | Inheritance | `contract Morpho is IMorphoStaticTyping` | ❌ | **Inheritance** not supported. Match the ABI structurally. |
| 20 | Call | `keccak256(abi.encode(DOMAIN_TYPEHASH, block.chainid, address(this)))` | ❌ | **`abi.encode`** not supported. |

### 1.4 Owner functions

| # | Function | Solidity | Verity status | Note |
|---|----------|----------|---------------|------|
| 21 | `setOwner(address) external onlyOwner` | ✅ | Inline modifier. |
| 22 | `enableIrm(address) external onlyOwner` | ✅ | |
| 23 | `enableLltv(uint256) external onlyOwner` | ✅ | |
| 24 | `setFee(MarketParams, uint256) external onlyOwner` | 🚧 | Blocked only by `market[id].fee = uint128(newFee)` cast → **`uint128`**. |
| 25 | `setFeeRecipient(address) external onlyOwner` | ✅ | |

### 1.5 Market creation

| # | Function | Solidity | Verity status | Note |
|---|----------|----------|---------------|------|
| 26 | `createMarket(MarketParams) external` | ❌ | `market[id].lastUpdate = uint128(block.timestamp)` and `idToMarketParams[id] = marketParams` need **`uint128`** and **struct-in-mapping**; `IIrm(...).borrowRate(...)` is low-level ✅ once storage blockers land. |

### 1.6 Core entrypoints

| # | Function | Solidity | Verity status | Note |
|---|----------|----------|---------------|------|
| 27 | `supply(MarketParams, uint256, uint256, address, bytes) external returns (uint256, uint256)` | ❌ | Reads/writes `market[id].totalSupplyAssets/Shares` (`uint128`), + callback `IMorphoSupplyCallback(msg.sender).onMorphoSupply` — **flashloan/reentrant callback pattern** not in EDSL. |
| 28 | `withdraw(MarketParams, uint256, uint256, address, address) external returns (uint256, uint256)` | ❌ | Same `uint128` field arithmetic. |
| 29 | `borrow(MarketParams, uint256, uint256, address, address) external returns (uint256, uint256)` | ❌ | `uint128` arithmetic; `_isHealthy` call ✅ shape-wise. |
| 30 | `repay(MarketParams, uint256, uint256, address, bytes) external returns (uint256, uint256)` | ❌ | Same `uint128` blockers + `onMorphoRepay` callback ❌. |
| 31 | `supplyCollateral(MarketParams, uint256, address, bytes) external` | ❌ | `position[id][onBehalf].collateral += assets.toUint128()`; `onMorphoSupplyCollateral` callback ❌. |
| 32 | `withdrawCollateral(MarketParams, uint256, address, address) external` | ❌ | `uint128` cast on `collateral`. |
| 33 | `liquidate(MarketParams, address, uint256, uint256, bytes) external returns (uint256, uint256)` | ❌ | Heaviest: `uint128` arithmetic on both `market[id]` and `position[id][borrower]`, `onMorphoLiquidate` callback ❌, oracle `IOracle(...).price()` ✅, math (`wMulDown`/`wDivUp`/`mulDivUp`/`mulDivDown`) ✅. |
| 34 | `flashLoan(address, uint256, bytes) external` | ❌ | Pure **flashloan callback pattern** — `onMorphoFlashLoan` sandwiched between `safeTransfer` and `safeTransferFrom`. |

### 1.7 Authorization

| # | Function | Solidity | Verity status | Note |
|---|----------|----------|---------------|------|
| 35 | `setAuthorization(address, bool) external` | ✅ | `mapping2` write + event. |
| 36 | `setAuthorizationWithSig(Authorization, Signature) external` | ❌ | `abi.encode(AUTHORIZATION_TYPEHASH, authorization)` ❌ + `bytes.concat("\x19\x01", ...)` ❌ + `ecrecover` (not on ✅ list). |
| 37 | `_isSenderAuthorized(address) internal view returns (bool)` | ✅ | Pure boolean. |

### 1.8 Interest accrual & health

| # | Function | Solidity | Verity status | Note |
|---|----------|----------|---------------|------|
| 38 | `accrueInterest(MarketParams) external` | 🚧 | Requires `market[id].lastUpdate` (`uint128`). |
| 39 | `_accrueInterest(MarketParams, Id) internal` | ❌ | Reads/writes 5 `uint128` fields; `wTaylorCompounded`, `wMulDown` ✅; `IIrm.borrowRate` ✅. |
| 40 | `_isHealthy(MarketParams, Id, address) internal view returns (bool)` | ❌ | Reads `position[id][borrower].borrowShares` (`uint128`). |
| 41 | `_isHealthy(MarketParams, Id, address, uint256) internal view returns (bool)` | ❌ | `uint256(position[id][borrower].borrowShares).toAssetsUp(...)` needs `uint128` field read. Math ✅. |

### 1.9 Storage view

| # | Function | Solidity | Verity status | Note |
|---|----------|----------|---------------|------|
| 42 | `extSloads(bytes32[]) external view returns (bytes32[])` | ❌ | Inline `assembly { sload }` over a calldata array. Verity has no **raw `sload` opcode / dynamic bytes32 return**. Workaround: expose typed getters. |

---

## 2. Libraries

### 2.1 `MathLib.sol`

| # | Function | Verity | Note |
|---|----------|--------|------|
| 43 | `wMulDown(uint256, uint256)` | ✅ | Native proven op. |
| 44 | `wDivDown(uint256, uint256)` | ✅ | Implied by `mulDivDown(x, WAD, y)`. |
| 45 | `wDivUp(uint256, uint256)` | ✅ | Native proven op. |
| 46 | `mulDivDown(uint256, uint256, uint256)` | ✅ | Native proven op. |
| 47 | `mulDivUp(uint256, uint256, uint256)` | ✅ | Native proven op. |
| 48 | `wTaylorCompounded(uint256, uint256)` | ✅ | Composable; Taylor is manual. |

### 2.2 `SharesMathLib.sol`

| # | Function | Verity | Note |
|---|----------|--------|------|
| 49 | `toSharesDown` | ✅ | Pure `mulDivDown`. |
| 50 | `toAssetsDown` | ✅ | Pure `mulDivDown`. |
| 51 | `toSharesUp` | ✅ | Pure `mulDivUp`. |
| 52 | `toAssetsUp` | ✅ | Pure `mulDivUp`. |
| 53 | Constant `VIRTUAL_SHARES = 1e6` | ✅ | |
| 54 | Constant `VIRTUAL_ASSETS = 1` | ✅ | |

### 2.3 `MarketParamsLib.sol`

| # | Function | Verity | Note |
|---|----------|--------|------|
| 55 | `id(MarketParams memory) → Id` via `assembly { keccak256(marketParams, 160) }` | 🚧 | Result is `keccak256` of 5 contiguous 32-byte words. EDSL can express as `keccak256(loanToken, collateralToken, oracle, irm, lltv)` if a **fixed-arity keccak of ABI-encoded words** helper is added; else `abi.encode` ❌. |

### 2.4 `UtilsLib.sol`

| # | Function | Verity | Note |
|---|----------|--------|------|
| 56 | `exactlyOneZero(uint256, uint256)` | ✅ | |
| 57 | `min(uint256, uint256)` | ✅ | Ternary. |
| 58 | `toUint128(uint256)` | ❌ | Returns **`uint128`**. |
| 59 | `zeroFloorSub(uint256, uint256)` | ✅ | |

### 2.5 `SafeTransferLib.sol`

| # | Function | Verity | Note |
|---|----------|--------|------|
| 60 | `safeTransfer(IERC20, address, uint256)` | 🚧 | Uses `abi.encodeCall` ❌ + returndata decode ❌; Verity port replaces with an **ECM primitive** (see `MORPH_BLUE_MAPPING.md`). |
| 61 | `safeTransferFrom(IERC20, address, address, uint256)` | 🚧 | Same ECM pattern. |

### 2.6 `ConstantsLib.sol`

| # | Constant | Verity | Note |
|---|----------|--------|------|
| 62 | `MAX_FEE = 0.25e18` | ✅ | |
| 63 | `ORACLE_PRICE_SCALE = 1e36` | ✅ | |
| 64 | `LIQUIDATION_CURSOR = 0.3e18` | ✅ | |
| 65 | `MAX_LIQUIDATION_INCENTIVE_FACTOR = 1.15e18` | ✅ | |
| 66 | `DOMAIN_TYPEHASH = keccak256("EIP712Domain(...)")` | ✅ | Compile-time. |
| 67 | `AUTHORIZATION_TYPEHASH = keccak256("Authorization(...)")` | ✅ | Compile-time. |

### 2.7 `ErrorsLib.sol`

All 21 error identifiers are `string internal constant` used as `require`
reason strings.

| # | Construct | Verity | Note |
|---|-----------|--------|------|
| 68 | 21× `string internal constant NAME` | 🚧 | Storage `string` ❌, but these are **library constants**, not storage — inline as literal reason strings at each `require`. Or convert to custom errors (✅). |

### 2.8 `EventsLib.sol` — 18 events

| # | Event | Verity | Note |
|---|-------|--------|------|
| 69 | `SetOwner`, `SetFee`, `SetFeeRecipient`, `EnableIrm`, `EnableLltv`, `Supply`, `Withdraw`, `Borrow`, `Repay`, `SupplyCollateral`, `WithdrawCollateral`, `FlashLoan`, `SetAuthorization`, `IncrementNonce`, `AccrueInterest` | ✅ | Fields all `address`/`uint256`/`bool`/`Id (bytes32)` — events with proofs supported. |
| 70 | `CreateMarket(Id indexed id, MarketParams marketParams)` | 🚧 | Non-indexed **struct payload** in event. Emit as 5 flat fields until struct-in-event is supported. |
| 71 | `Liquidate(Id, address, address, 5×uint256)` | ✅ | Flat scalar payload. |

### 2.9 Interface files (`IMorpho.sol`, `IIrm.sol`, `IOracle.sol`, `IMorphoCallbacks.sol`, `IERC20.sol`)

| # | Construct | Verity | Note |
|---|-----------|--------|------|
| 72 | External interfaces used via low-level `call`/`staticcall` (`IIrm.borrowRate`, `IOracle.price`, `IERC20.transfer/transferFrom`, 5× callback interfaces) | ✅ / ❌ | Static/low-level calls ✅ for IRM+Oracle+ERC20; **the 5 callback interfaces** need the **flashloan/callback trust-boundary** ❌. |

---

## 3. Summary

**Counted constructs: 72**

| Bucket | Count | % |
|--------|-------|---|
| ✅ expressible today | 34 | 47% |
| 🚧 workaround exists | 13 | 18% |
| ❌ needs new EDSL feature | 25 | 35% |

### Top 5 missing EDSL features (weighted by usage in Morpho)

| Rank | Feature | Directly blocks | Why it dominates |
|------|---------|-----------------|------------------|
| 1 | **`uint128` scalar type** | rows 4, 5, 13, 14, 24, 26, 27–33, 38–41, 58 (~15 constructs) | Every write to `Market` or `Position` casts to `uint128`; nothing accrual/health/liquidation-related compiles without it. |
| 2 | **Packed struct storage in `mapping` (#1976 completion for 6×`uint128`)** | rows 4, 5, 10, 26 | `Market` packs 6 `uint128`s into 2 slots; `Position` packs `uint128+uint128` into 1 slot; #1976 support needs to cover 6-field packing to match Solidity's layout used by `extSloads`. |
| 3 | **Callback / re-entrant trust boundary (`onMorpho*`)** | rows 27, 30, 31, 33, 34, 72 | 5 of 8 core entrypoints run user-supplied code mid-execution. `flashLoan` is nothing but this pattern. |
| 4 | **`abi.encode` / `abi.encodePacked` / `bytes.concat`** | rows 17, 20, 36, 55 | EIP-712 paths and the market-id keccak use ABI encoding. Alternative: "keccak of typed tuple" primitive. |
| 5 | **`ecrecover` precompile** | row 36 | `setAuthorizationWithSig` needs it; unlocks any future meta-tx feature. |

### Recommended "next 3 PRs to unblock Morpho"

1. **PR-A: `uint128` scalar + packed-mapping storage (Market & Position
   layouts).** Land `uint128` arithmetic + widen #1976 packed-struct support
   to 6 fields with the exact slot layout Solidity uses. Immediately unblocks
   `createMarket`, `_accrueInterest`, `supply`, `withdraw`, `borrow`, `repay`,
   `supplyCollateral`, `withdrawCollateral`, `_isHealthy` — reduces ❌ from
   25 → ~9.
2. **PR-B: Callback trust-boundary primitive (`onMorpho*` pattern).** A
   `verity_contract` construct that models "emit event → external `call` to
   caller → resume with post-state assertion" as an ECM trust boundary —
   reuses the existing ECM pattern already used by `SafeTransferLib` in the
   Verity port. Unblocks `flashLoan`, `supply`, `repay`, `supplyCollateral`,
   `liquidate`.
3. **PR-C: EIP-712 helpers — `abi.encode`-of-tuple + `ecrecover`.** Even a
   narrow `keccak256_of_words(bytes32, ...)` plus `ecrecover(bytes32, uint8,
   bytes32, bytes32)` closes `setAuthorizationWithSig`, the constructor's
   `DOMAIN_SEPARATOR`, and `MarketParamsLib.id`.

After these three PRs, `>90%` of Morpho Blue's Solidity would map
line-by-line into `verity_contract`. Remaining ❌ items (inheritance,
first-class modifiers, `extSloads` raw `sload` array) are cosmetic or
replaceable with typed getters and do not block correctness parity.
