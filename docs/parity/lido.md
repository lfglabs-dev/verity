# Lido StakingRouter v3 — Verity EDSL parity gap map

**Status:** draft — best-effort. The Solidity source is NOT in
`lfglabs-dev/lido-srv3-proof-closure` (that repo is a LaTeX report package).
The Solidity mapped here lives in the upstream Lido monorepo `lidofinance/core`
at the exact revision named in the report's `content/05-reproducibility.tex`:

- Repo: `lidofinance/core` (branch: `develop`, PR
  [#1811 — Staking Router V3](https://github.com/lidofinance/core/pull/1811))
- Commit: `d088bbc2deac9913b68036d73d35c37aa6279b90`
- Files mapped (from the report's own "Source anchor examples" list):
  - `contracts/0.8.25/sr/StakingRouter.sol` (~1158 loc)
  - `contracts/0.8.25/sr/SRLib.sol` (~932 loc, external library)
  - `contracts/0.8.25/sr/SRStorage.sol`, `SRTypes.sol`, `SRUtils.sol`, `ISRBase.sol`
  - `contracts/0.8.25/TopUpGateway.sol` (~424 loc)
  - `contracts/0.8.9/oracle/AccountingOracle.sol` (~917 loc)
  - `contracts/0.4.24/Lido.sol` (~1558 loc, buffer / reserve / `withdrawDepositableEther`)

**Support matrix legend** (from
[verity #1724](https://github.com/lfglabs-dev/verity/issues/1724)):

- ✅ expressible today in `verity_contract`
- 🚧 expressible with a workaround (noted)
- ❌ requires a new EDSL feature (feature name noted)

**Verity type baseline used below.** ✅: `uint256`, `int256`, `uint8`,
`address`, `bytes32`, `bool`, single mapping, `mapping2`, simple events, custom
errors with scalar payloads, `require`, bounded `for`, `if/else`, ternary,
low-level `call`/`staticcall`/`delegatecall` (no proof coverage). ❌:
`uint128/64/32/24/16`, `int128`, `bytes4/20`, `enum`, storage `string`/`bytes`,
top-level `struct` as storage root, `mapping` depth ≥ 3 (no proof),
multiple inheritance, modifier postludes, `abi.encode`/`abi.encodePacked`,
`try/catch`, `while`, `break/continue`, `CREATE`/`CREATE2`, `transfer`/`send`,
`receive`/`fallback`.

The report itself scopes to six accounting properties (SRV3-P1 … P6).
Constructs outside that scope are still listed so gaps can be counted honestly.

---

## 1. `contracts/0.8.25/sr/SRTypes.sol`

### 1.1 Enums

| Construct | Signature | Status | Notes / needed feature |
|---|---|---|---|
| enum `StakingModuleStatus` | `{Active, DepositsPaused, Stopped}` | ✅ | Native uint8-backed enum declarations, members, and checked casts (#2088). |

### 1.2 Interfaces (referenced, not implemented)

| Construct | Signature | Status | Notes |
|---|---|---|---|
| `interface ILido` | `getDepositableEther() view returns (uint256)`, `withdrawDepositableEther(uint256,uint256)` | 🚧 | External-call interface. Verity has no `interface` decl but the calls can be modeled with typed low-level `call` — no proof coverage |
| `interface IAccountingOracle` | `getProcessingState() returns (9-tuple)`, `getLastProcessingRefSlot()` | 🚧 | 9-value return tuple — Verity has partial multi-return; no destructuring assignment |

### 1.3 Structs (used as storage or in mappings)

| Struct | Fields (widths) | Status | Feature gap |
|---|---|---|---|
| `StakingModuleConfig` (calldata only) | 7× `uint256` | ✅ | Fits Tuple encoding |
| `StakingModule` (legacy, in storage during migration) | `uint24,address,uint16,uint16,uint16,uint8,string,uint64,uint256,uint256,uint16,uint64,uint64,uint8,uint64` | ❌ | `uint24`, `uint16`, `uint64`, `uint8`, storage `string`, storage struct root |
| `ModuleStateConfig` (1 storage slot, packed) | `address,uint16,uint16,uint16,uint16,StakingModuleStatus(enum),uint8` | ❌ | packed `uint16`+`enum`+`uint8` in one slot — needs `uint16`, `enum`, packed-field support |
| `ModuleStateDeposits` (1 slot) | 4× `uint64` | ❌ | `uint64` |
| `ModuleStateAccounting` (1 slot) | 2× `uint64` | ❌ | `uint64` |
| `RouterStateAccounting` (1 slot) | `uint64` | ❌ | `uint64` |
| `ModuleState` (top-level storage struct) | `config, deposits, accounting, string name` | ❌ | storage `string`, nested storage structs |
| `RouterState` (top-level storage struct) | `mapping(uint256=>ModuleState), EnumerableSet.UintSet, RouterStateAccounting, bytes32, uint24 lastModuleId` | ❌ | top-level struct storage root, `uint24`, EnumerableSet library-typed storage |
| `StakingModuleSummary` (memory) | 3× `uint256` | ✅ | Tuple/return |
| `NodeOperatorSummary` (memory) | 8× `uint256` | ✅ | Tuple/return |
| `StakingModuleDigest` (memory return) | 2 uint256 + `StakingModule` + `StakingModuleSummary` | ❌ | nested struct memory returns |
| `NodeOperatorDigest` (memory return) | `uint256, bool, NodeOperatorSummary` | 🚧 | Flatten to tuple |
| `ValidatorsCountsCorrection` (memory) | 4× `uint256` | ✅ | Tuple |
| `ValidatorExitData` (memory) | `uint256, uint256, bytes` | 🚧 | `bytes` ABI-only in Verity; OK if only calldata/memory |

---

## 2. `contracts/0.8.25/sr/ISRBase.sol` (events + errors)

### 2.1 Events

| Event | Signature | Status | Notes |
|---|---|---|---|
| `StakingModuleAdded` | `(uint256 indexed, address, string, address)` | 🚧 | indexed dynamic events are supported; `string` in payload is ABI-only |
| `StakingModuleShareLimitSet` | `(uint256 indexed, uint256, uint256, address)` | ✅ | |
| `StakingModuleFeesSet` | `(uint256 indexed, uint256, uint256, address)` | ✅ | |
| `StakingModuleMaxDepositsPerBlockSet` | `(uint256 indexed, uint256, address)` | ✅ | |
| `StakingModuleMinDepositBlockDistanceSet` | `(uint256 indexed, uint256, address)` | ✅ | |
| `StakingModuleStatusSet` | `(uint256 indexed, StakingModuleStatus, address)` | ✅ | Enum event payloads erase to `uint8` in the ABI. |
| `WithdrawalCredentialsSet` | `(bytes32, address)` | ✅ | |
| `StakingRouterETHDeposited` | `(uint256 indexed, uint256)` | ✅ | |
| `DepositableEthReceived` | `(uint256)` | ✅ | |
| `ExitedAndStuckValidatorsCountsUpdateFailed` | `(uint256 indexed, bytes)` | 🚧 | dynamic `bytes` event supported |
| `RewardsMintedReportFailed` | `(uint256 indexed, bytes)` | 🚧 | same |
| `StakingModuleExitedValidatorsIncompleteReporting` | `(uint256 indexed, uint256)` | ✅ | |
| `WithdrawalsCredentialsChangeFailed` | `(uint256 indexed, bytes)` | 🚧 | dynamic `bytes` |
| `StakingModuleExitNotificationFailed` | `(uint256 indexed, uint256 indexed, bytes)` | 🚧 | dynamic `bytes` |

### 2.2 Errors (custom, scalar payloads unless noted)

| Error | Payload | Status |
|---|---|---|
| `InvalidAmountGwei`, `NotAuthorized`, `ZeroAddress`, `ZeroArgument`, `ArraysLengthMismatch`, `OracleExtraDataNotSubmitted` | none | ✅ |
| `InvalidReportData` | `(uint256)` | ✅ |
| `ReportedExitedValidatorsExceedDeposited` | `(uint256, uint256)` | ✅ |
| `UnexpectedCurrentValidatorsCount` | `(uint256, uint256)` | ✅ |
| `UnexpectedFinalExitedValidatorsCount` | `(uint256, uint256)` | ✅ |
| `UnrecoverableModuleError`, `ExitedValidatorsCountCannotDecrease`, `DirectETHTransfer`, `ModuleReturnExceedTarget`, `StakingModuleStatusTheSame`, `EmptyKeysList`, `WrongPubkeyLength`, `AmountNotAlignedToGwei`, `AllocationExceedsLimit`, `ZeroDeposits`, `StakingModuleAddressExists`, `StakingModulesLimitExceeded`, `StakingModuleWrongName`, `StakingModuleUnregistered`, `StakingModuleNotActive`, `WrongWithdrawalCredentialsType`, `InvalidPriorityExitShareThreshold`, `InvalidMinDepositBlockDistance`, `InvalidMaxDepositPerBlockValue`, `InvalidStakeShareLimit`, `InvalidFeeSum`, `InconsistentFeeSum` | none | ✅ |
| `UnexpectedModuleId` | `(uint256, uint256)` | ✅ |

---

## 3. `contracts/0.8.25/sr/StakingRouter.sol`

### 3.1 Top-level construct

| Construct | Status | Feature gap |
|---|---|---|
| `contract StakingRouter is ISRBase, AccessControlEnumerableUpgradeable` | ❌ | inheritance (`is X, Y`) — no Verity equivalent; must flatten |

### 3.2 State constants & immutables

| Var | Type | Status | Notes |
|---|---|---|---|
| 9× `bytes32 public constant *_ROLE = keccak256(...)` | `bytes32` | ✅ | keccak of literal string OK |
| `FEE_PRECISION_POINTS` | `uint256 constant` | ✅ | |
| `PUBKEY_LENGTH` | `uint64 constant` | ❌ | `uint64` — workaround: `uint256` |
| `DEPOSIT_CONTRACT`, `LIDO`, `LIDO_LOCATOR` | `I* immutable` | 🚧 | Verity has immutables for scalars; `interface` type as `address` |
| `MAX_EFFECTIVE_BALANCE_WC_TYPE_01/02` | `uint256 immutable` | ✅ | |

### 3.3 Constructor & initializers

| Function | Signature | Status | Notes |
|---|---|---|---|
| `constructor(address,address,address,uint256,uint256)` | — | ✅ | Verity supports constructor + immutable init |
| `initialize(address _admin, bytes32 _wc) external reinitializer(4)` | — | ❌ | `reinitializer(4)` modifier — modifier system missing |
| `finalizeUpgrade_v4() external reinitializer(4)` | — | ❌ | modifier + inline delete of legacy role storage |

### 3.4 Functions (grouped)

For brevity: `external onlyRole(X)` in every management function collapses into
"❌ modifier system".

| Function (signature abbreviated) | Visibility / mut. | Status | Notes / gap |
|---|---|---|---|
| `INITIAL_DEPOSIT_SIZE() view returns (uint256)` | external | ✅ | |
| `TOTAL_BASIS_POINTS() pure returns (uint256)` | external | ✅ | |
| `MAX_STAKING_MODULES_COUNT() pure returns (uint256)` | external | ✅ | |
| `MAX_STAKING_MODULE_NAME_LENGTH() pure returns (uint256)` | external | ✅ | |
| `_getStorageRoleMembersOld() private pure returns (mapping storage $)` | private pure | ❌ | inline assembly + returning `mapping storage` — needs storage-pointer + assembly |
| `addStakingModule(string calldata,address,StakingModuleConfig calldata)` | external, `onlyRole` | 🚧 | body OK once modifier lowered |
| `updateStakingModule(uint256,uint256×6)` | external, `onlyRole` | 🚧 | 7 scalar args |
| `updateAllStakingModulesFees(uint256[] calldata,uint256[] calldata)` | external | 🚧 | calldata arrays OK, bounded for |
| `updateModuleShares(uint256, uint16, uint16)` | external | ❌ | `uint16` params |
| `updateTargetValidatorsLimits(uint256, uint256, uint256, uint256)` | external | 🚧 | forwards to module via `call` |
| `reportRewardsMinted(uint256[], uint256[])` | external | 🚧 | SRV3-P4/P5 core path |
| `updateExitedValidatorsCountByStakingModule(uint256[], uint256[])` | external | 🚧 | |
| `reportValidatorBalancesByStakingModule(uint256[], uint256[])` | external | 🚧 | SRV3-P3 core path; writes `uint64` balance sums — needs `uint64` |
| `validateReportValidatorBalancesByStakingModule(uint256[], uint256[])` | external view | ✅ | pure array validation |
| `reportStakingModuleExitedValidatorsCountByNodeOperator(uint256, bytes, bytes)` | external | 🚧 | `bytes` calldata OK |
| `unsafeSetExitedValidatorsCount(uint256,uint256,bool,ValidatorsCountsCorrection)` | external | 🚧 | struct-by-value calldata (tuple) |
| `onValidatorsCountsByNodeOperatorReportingFinished()` | external | 🚧 | walk `for` over modules |
| `decreaseStakingModuleVettedKeysCountByNodeOperator(uint256, bytes, bytes)` | external | 🚧 | delegates to module (call) |
| `reportValidatorExitDelay(uint256,uint256,uint256,bytes,uint256)` | external | 🚧 | |
| `onValidatorExitTriggered(ValidatorExitData[] calldata,uint256,uint256)` | external | 🚧 | struct array |
| `getStakingModules() view returns (StakingModule[])` | external | ❌ | returns array of legacy struct with narrow ints + `string` |
| `getStakingModuleStateConfig / …StateDeposits / …StateAccounting(uint256)` | external view | ❌ | returns packed narrow-int structs |
| `getStakingModuleIds() view returns (uint256[])` | external | ✅ | |
| `getStakingModule(uint256) view returns (StakingModule)` | external | ❌ | same struct |
| `getStakingModulesCount() view returns (uint256)` | external | ✅ | |
| `hasStakingModule(uint256) view returns (bool)` | public | ✅ | |
| `getStakingModuleStatus(uint256) view returns (StakingModuleStatus)` | public | ✅ | Enum returns erase to `uint8` in the ABI. |
| `getContractVersion() view returns (uint256)` | external | ✅ | |
| `getStakingModuleSummary` / `getNodeOperatorSummary` | external view | ✅ | scalar tuple returns |
| `getAllStakingModuleDigests / getStakingModuleDigests(uint256[])` | external view | ❌ | nested-struct memory arrays |
| `getAllNodeOperatorDigests / getNodeOperatorDigests(...)` | external view | 🚧 | flatten to tuple[] |
| `setStakingModuleStatus(uint256, StakingModuleStatus)` | external `onlyRole` | ✅ | Enum parameters and storage values are supported. |
| `getStakingModuleIsStopped / IsDepositsPaused / IsActive` | external view returns (bool) | ❌ | derived from enum status |
| `getStakingModuleNonce / LastDepositBlock / MinDepositBlockDistance / MaxDepositsPerBlock` | external view returns (uint256) | 🚧 | value stored as `uint64`; cast up |
| `getStakingModuleActiveValidatorsCount(uint256) view returns (uint256, uint256)` | external | ✅ | |
| `getStakingModuleWithdrawalCredentials(uint256) view returns (bytes32)` | external | ✅ | |
| `getStakingModuleMaxDepositsCount(uint256, uint256) view returns (uint256)` | external | ✅ | |
| `canDeposit(uint256) view returns (bool)` | external | ✅ | |
| `receiveDepositableEther() external payable` | external payable | ❌ | payable function needs `receive`/`fallback`/payable modeling (partial) |
| `topUp(uint256, IStakingModuleV2.TopUpsData calldata, bytes calldata)` | external, `onlyRole`, calls out | 🚧 | ABI arrays OK; per-key allocation loop; `abi.encodePacked` on `bytes32 wc` (❌); modifier ❌ |
| `_validateTopUpInputs(uint256, uint256, uint256[] calldata) internal pure` | internal pure | ✅ | |
| `getStakingFeeAggregateDistribution() view returns (uint96 total, uint96 mod, uint96 treas, uint256 prec)` | external | ❌ | `uint96` × 3 |
| `getStakingRewardsDistribution() view returns (address[], uint256[], uint96[], uint96 totalFee, uint256 prec)` | external | ❌ | `uint96` × 2 + `uint96[]` (SRV3-P5 anchor) |
| `getModuleValidatorsBalance(uint256) view returns (uint256)` | external | 🚧 | Wraps `uint64` internal store |
| `getTotalModulesValidatorsBalance() view returns (uint256)` | external | 🚧 | Same |
| `_computeModuleFee(uint256, uint256, uint256, uint16) view returns (uint256)` | internal | ❌ | `uint16` arg |
| `getTotalFeeE4Precision() view returns (uint16)` | external | ❌ | `uint16` return |
| `getStakingFeeAggregateDistributionE4Precision() view returns (uint16, uint16, uint16)` | external | ❌ | `uint16` returns |
| `getDepositAllocations(uint256, bool) view returns (uint256[])` | external | ✅ | |
| `deposit(uint256, bytes calldata) external` | external | 🚧 | SRV3-P2 core path; body uses `address(this).balance` (❌), `abi.encodePacked` (❌), external `call` (🚧); enum comparison ❌ |
| `setWithdrawalCredentials(bytes32) external onlyRole` | external | 🚧 | modifier + notifying loop |
| `getWithdrawalCredentials() public view returns (bytes32)` | public view | ✅ | |
| `_setWithdrawalCredentials(bytes32) internal` | internal | ✅ | |
| `_getWithdrawalCredentialsWithType(uint8) internal view returns (bytes32)` | internal | ✅ | |
| `_updateModuleLastDepositState(uint256, uint256) internal` | internal | 🚧 | writes `uint64 lastDepositBlock` — needs `uint64` |
| `_getModuleDepositAllocation(uint256, uint256, bool) view returns (uint256)` | internal | ✅ | |
| `_getStakingModuleNodeOperatorsCount / …Active…Count(IStakingModule) internal view` | internal | 🚧 | external `staticcall` |
| `_getStakingModuleNodeOperatorIds(IStakingModule, uint256, uint256) view returns (uint256[])` | internal | 🚧 | staticcall |
| `_getStakingModuleNodeOperatorIsActive(IStakingModule, uint256) view returns (bool)` | internal | 🚧 | staticcall |
| `_getModuleState / _getModuleStateCompat / _getStakingModuleSummary / …Struct / _getNodeOperatorSummary` | internal view | 🚧/❌ | Compat variants build legacy struct with narrow ints |
| `_getAccountingOracle / _getTopUpGateway / _getDepositSecurityModule() internal view returns (address)` | internal | ✅ | via locator staticcall |
| `_checkAppAuth(address)` | internal view | ✅ | |
| `_getConfig() private view returns (SRLib.Config)` | private | ✅ | |
| `_toE4Precision(uint256, uint256) pure returns (uint16)` | internal pure | ❌ | `uint16` return |

### 3.5 Modifiers used but not declared here

- `onlyRole(bytes32)` (from OZ AccessControl) — used on ~20 external funcs — ❌ modifier system + inheritance
- `reinitializer(4)` — used on `initialize`, `finalizeUpgrade_v4` — ❌ modifier system

---

## 4. `contracts/0.8.25/sr/SRLib.sol` (external library)

Library used through `using X for Y` — Verity has no library concept; would
inline.

| Construct | Status | Feature gap |
|---|---|---|
| `library SRLib` | ❌ | `library` decl — must inline |
| `struct Config { uint256, uint256 }` | ✅ | scalar tuple |
| `struct ModuleParamsCache { uint256, uint256, uint16, StakingModuleStatus(enum), uint8 }` | ❌ | `uint16` + enum |
| `_migrateStorage(uint256)` | ❌ | `keccak256` of literal (✅), `delete` on storage slot (❌), `abi.encode`/`abi.encodePacked` (❌), inline assembly slot compute (❌), builds/writes `uint64` fields + `uint24 lastModuleId` (❌), storage `string name` (❌) |
| `_getStorageStakingModulesMapping / _getStorageStakingIndicesMapping` | ❌ | returns `mapping storage` via inline assembly |
| `_addModule(address, string calldata, StakingModuleConfig calldata) returns (uint256)` | ❌ | writes storage `string name`, `uint24 lastModuleId++`, packs `ModuleStateConfig` |
| `_validateShareParams(uint256, uint256) pure` | ✅ | |
| `_updateModuleParams(uint256, uint256×6)` | ❌ | writes `uint16` fields into packed slot |
| `_requireConsistentFeeSum(uint256, uint256, uint256) view` | ✅ | bounded `for` + `require` |
| `_updateAllModuleFees(uint256[] calldata, uint256[] calldata)` | ❌ | writes packed `uint16` fields |
| `_updateModuleShares(uint256, uint256, uint256)` | ❌ | writes packed `uint16` fields |
| `_setModuleStatus(uint256, StakingModuleStatus) returns (bool)` | ❌ | enum arg + writes enum-in-packed-struct |
| `_getStakingModuleSummary(IStakingModule) view returns (uint256, uint256, uint256)` | 🚧 | staticcall (no proof) |
| `_getDepositAllocations(Config calldata, uint256, bool) view returns (uint256, uint256[])` | ✅ | SRV3-P2 anchor — pure array/loop |
| `_getModuleDepositAllocation(uint256, uint256, bool) view returns (uint256)` | ✅ | |
| `_getModulesAllocationAndCapacity(Config calldata, uint256, bool) view returns (uint256[], ModuleParamsCache[])` | ❌ | `ModuleParamsCache[]` contains `uint16` + enum |
| `_reportValidatorExitDelay(uint256, uint256, uint256, bytes calldata, uint256)` | 🚧 | forwarded call |
| `_onValidatorExitTriggered(ValidatorExitData[] calldata, uint256, uint256)` | 🚧 | |
| `_reportRewardsMinted(uint256[] calldata, uint256[] calldata)` | 🚧 | SRV3-P4/P5 anchor: try/catch pattern via low-level `call` + `returndataSize` |
| `_onValidatorsCountsByNodeOperatorReportingFinished()` | 🚧 | loop + call |
| `_decreaseStakingModuleVettedKeysCountByNodeOperator / _reportStakingModuleOperatorExitedValidators / _updateExitedValidatorsCountByStakingModule` | ❌ | Read/write `uint64 exitedValidatorsCount` |
| `_unsafeSetExitedValidatorsCount(...)` | ❌ | Same `uint64` gap |
| `_validateReportValidatorBalancesByStakingModule(uint256[], uint256[]) view` | ✅ | SRV3-P3 anchor |
| `_reportValidatorBalancesByStakingModule(uint256[], uint256[])` | ❌ | SRV3-P3 write path: writes `uint64 validatorsBalanceGwei` |
| `_updateModuleLastDepositState(uint256)` | ❌ | writes `uint64 lastDepositBlock/At` |
| `_notifyStakingModulesOfWithdrawalCredentialsChange()` | 🚧 | loop + low-level `call` |
| `_checkOperatorsReportData(bytes calldata, bytes calldata) internal pure` | 🚧 | slicing `bytes calldata` via assembly `calldataload` |

---

## 5. `contracts/0.8.25/sr/SRStorage.sol` (thin storage-slot helper library)

| Construct | Status | Feature gap |
|---|---|---|
| `library SRStorage` | ❌ | `library` |
| `bytes32 constant ROUTER_STORAGE_POSITION = keccak256(abi.encode(uint256(keccak256(abi.encodePacked("..."))) - 1)) & ~bytes32(uint256(0xff))` | ❌ | ERC-7201 slot derivation uses `abi.encode` + `abi.encodePacked` |
| `getRouterState() pure returns (RouterState storage $)` | ❌ | inline assembly `$.slot := _position` + top-level struct storage root |
| All `getModuleState`, `addModuleId`, `getModulesCount`, `getModuleIdInnerPosition`, `isModuleExists` | ❌ | OZ `EnumerableSet.UintSet` — 3-deep mapping style; Verity lacks `mappingChain` proof |

---

## 6. `contracts/0.8.25/TopUpGateway.sol`

| Construct | Status | Feature gap |
|---|---|---|
| `struct Storage { uint64, uint32, uint32, uint16, uint16, uint64, uint64 }` (packed one-slot) | ❌ | `uint64`, `uint32`, `uint16` |
| `bytes32 constant GATEWAY_STORAGE_POSITION` (ERC-7201) | ❌ | `abi.encode/Packed` |
| `uint256 constant PUBKEY_LENGTH = 48` | ✅ | |
| `uint256 constant FAR_FUTURE_EPOCH = type(uint64).max` | ❌ | `type(T).max` unavailable in EDSL |
| `uint256 immutable SLOTS_PER_EPOCH` | ✅ | |
| Roles `TOP_UP_ROLE`, `MANAGE_LIMITS_ROLE` | ✅ | |
| `constructor(uint64, uint256)` | ❌ | `uint64` arg |
| `topUp(TopUpsData calldata, ...)` | 🚧 | modifier `onlyRole` ❌; body reads `bytes32 wc` via external `staticcall`; uses `abi.encodePacked` on pubkey concat (❌) |
| `_verifyValidatorState(...)` | ❌ | EIP-4788 beacon root proof — Merkle/SSZ (out of scope) |
| `_computeTopUpLimit(Validator, uint64) view returns (uint256)` | ❌ | `uint64` arg |
| `_gatewayStorage() pure returns (Storage storage $)` | ❌ | inline asm + packed narrow-int storage struct |
| Events: `MaxValidatorsPerTopUpChanged / MinBlockDistanceChanged / LastTopUpChanged / MaxRootAgeChanged / TopUpBalanceLimitsChanged` | ✅ | |
| Errors `ZeroValue`, `TooLargeValue`, `RootIsTooOld`, `RootPrecedesLastTopUp`, `WrongArrayLength` | ✅ | |
| Error `ZeroArgument(string argument)` | ❌ | dynamic `string` payload |

---

## 7. `contracts/0.8.9/oracle/AccountingOracle.sol` (SRv3 balance-check path only)

| Construct | Status | Feature gap |
|---|---|---|
| `contract AccountingOracle is BaseOracle` | ✅ | flattened single inheritance; virtual overrides specialize at compile time |
| `initialize(...)` / `finalizeUpgrade_v5(uint256)` | ❌ | modifiers |
| `submitReportData(ReportData calldata, uint256)` | ❌ | large calldata struct with nested fields |
| `_checkStakingRouterModuleBalances(sanityChecker, data, timeElapsed)` (SRV3-P3 P4 anchor) | 🚧 | staticcall + bounded loop |
| `_normalizeStakingRouterValidatorBalancesToWei(uint256[])` | ✅ | pure multiplication |
| `_processStakingRouterExitedValidatorsByModule / …ValidatorBalancesByModule` | 🚧 | forwarded external calls |
| `_processExtraDataItems / _processExtraDataItem(bytes calldata, ExtraDataIterState)` | ❌ | slices `bytes calldata` via assembly `calldataload`, packs `bytes4` selectors, `while`-style |
| `_storageExtraDataProcessingState() pure returns (StorageExtraDataProcessingState storage r)` | ❌ | assembly slot pointer + storage struct |
| Storage struct `StorageExtraDataProcessingState` (packed) | ❌ | contains `uint64` fields |
| Events + errors (~15, mostly scalar) | ✅ | |

---

## 8. `contracts/0.4.24/Lido.sol` (buffer / reserve / withdraw path only)

Solidity 0.4.24 dialect — Verity targets 0.8.x — the accounting logic would
have to be re-expressed.

| Construct | Status | Feature gap |
|---|---|---|
| `contract Lido is Versioned, StETHPermit, AragonApp` (multiple inheritance) | ❌ | inheritance (deep) |
| `bytes32 constant BUFFERED_ETHER_POSITION` — packed slot `uint128 depositedPostReport | uint128 bufferedEther` | ❌ | `uint128`, packed 2×`uint128` |
| `bytes32 constant DEPOSITS_RESERVE_POSITION` (single `uint256` slot) | ✅ | ERC-1967 unstructured storage |
| `struct BufferedEtherAllocation { uint256 total, unfinalizedStETH, unreserved, depositsReserve, withdrawalsReserve }` (memory only) | ✅ | scalar tuple |
| `event DepositsReserveSet(uint256)` | ✅ | |
| `event ExternalBadDebtInternalized(uint256)` | ✅ | |
| `_getBufferedEtherAllocation() internal view returns (BufferedEtherAllocation)` (SRV3-P1 anchor) | ✅ | pure `min` arithmetic |
| `getDepositsReserve() external view returns (uint256)` | ✅ | |
| `getDepositableEther() external view returns (uint256)` | ✅ | |
| `withdrawDepositableEther(uint256, uint256) external` (SRV3-P1 anchor) | ❌ | writes `uint128 depositedPostReport` (packed) + 2300-gas `transfer`. Requires `uint128` + `transfer` |
| `receive() external payable` / `fallback()` | ❌ | receive/fallback |
| `_getBufferedEther() internal view returns (uint256)` (extracts low 128 bits) | ❌ | `uint128` + bitmask extraction |
| `_setBufferedEther(uint256) internal` | ❌ | `uint128` packed write |

---

## Summary

**Total top-level constructs counted:** 176

| Category | ✅ | 🚧 | ❌ | Total |
|---|---:|---:|---:|---:|
| Structs / Enums | 5 | 2 | 12 | 19 |
| State variables & constants | 12 | 3 | 8 | 23 |
| Events | 9 | 5 | 1 | 15 |
| Errors | 30 | 0 | 1 | 31 |
| Functions (external + internal + library) | 21 | 27 | 32 | 80 |
| Contract-level (inheritance, receive/fallback, modifiers-used) | 0 | 0 | 8 | 8 |
| **Total** | **77 (43.8%)** | **37 (21.0%)** | **62 (35.2%)** | **176** |

Only the SRv3-P1…P6 accounting core skews friendlier: ~55 % ✅ / 30 % 🚧 /
15 % ❌ — the ❌ items are concentrated in **`uint64` balance storage** and
**`enum` status gating**.

### Top 3 missing EDSL features weighted by usage count

1. **Narrow unsigned integer widths** (`uint64`, `uint16`, `uint32`, `uint24`,
   `uint96`, `uint128`) — hit in almost every storage struct and both SRV3
   core writes. **~45 distinct construct hits.** Blocks P3 write path and P1
   write path outright.
2. **`enum` support** — `StakingModuleStatus` in status gating (SRV3-P6),
   setters, getters, events, storage packing, args. **~14 construct hits.**
   Workaround exists (`Uint8`) but propagates through every signature and the
   packed slot.
3. **Modifier system + inheritance** — `onlyRole`, `reinitializer`, `is
   ISRBase, AccessControlEnumerableUpgradeable`. **~30 construct hits.** No
   in-block workaround today; must flatten.

Runner-ups: storage `string`, top-level storage structs, `abi.encode` /
`abi.encodePacked`, inline-assembly storage pointer resolution.

### Verdict on the six P0 properties

- **SRV3-P1 (reserve separation)** — math ✅; write side (`withdrawDepositableEther`, packed `uint128|uint128` slot) ❌ until `uint128`.
- **SRV3-P2 (exact 32 ETH pull)** — allocation math ✅; `deposit()` body ❌/🚧 (`abi.encodePacked(wc)`, beacon deposit).
- **SRV3-P3 (module-balance conservation)** — validation ✅; accepted-report write writes `uint64 validatorsBalanceGwei`. Blocked on `uint64`.
- **SRV3-P4 (report-before-reward)** — expressible once `uint64` reads exist.
- **SRV3-P5 (bounded rewards / fee alignment)** — invariant ✅; types (`uint96 totalFee`, `uint96[]`) ❌.
- **SRV3-P6 (status gates)** — depends on `enum StakingModuleStatus`; ❌ / 🚧 with `Uint8` shim.

**Net:** three of six properties can be *stated* today with modest workarounds
(P2, P4, P5 partial). P1, P3, P6 will not close without the top-3 EDSL
features.
