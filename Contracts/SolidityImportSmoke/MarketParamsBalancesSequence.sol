// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

type Id is bytes32;

struct MarketParams {
    address loanToken;
    address collateralToken;
    address oracle;
    address irm;
    uint256 lltv;
}

struct Position {
    uint256 supplyShares;
    uint128 borrowShares;
    uint128 collateral;
}

struct Market {
    uint128 totalSupplyAssets;
    uint128 totalSupplyShares;
    uint128 totalBorrowAssets;
    uint128 totalBorrowShares;
    uint128 lastUpdate;
    uint128 fee;
}

uint256 constant WAD = 1e18;

library MarketParamsLib {
    uint256 internal constant MARKET_PARAMS_BYTES_LENGTH = 5 * 32;

    function id(MarketParams memory marketParams) internal pure returns (Id marketParamsId) {
        assembly ("memory-safe") {
            marketParamsId := keccak256(marketParams, MARKET_PARAMS_BYTES_LENGTH)
        }
    }
}

library UtilsLib {
    function min(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := xor(x, mul(xor(x, y), lt(y, x)))
        }
    }

    function toUint128(uint256 x) internal pure returns (uint128) {
        require(x <= type(uint128).max, "max uint128 exceeded");
        return uint128(x);
    }

    function zeroFloorSub(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := mul(gt(x, y), sub(x, y))
        }
    }
}

library MathLib {
    function wMulDown(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivDown(x, y, WAD);
    }

    function mulDivDown(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y) / d;
    }

    function mulDivUp(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y + (d - 1)) / d;
    }

    function wTaylorCompounded(uint256 x, uint256 n) internal pure returns (uint256) {
        uint256 firstTerm = x * n;
        uint256 secondTerm = mulDivDown(firstTerm, firstTerm, 2 * WAD);
        uint256 thirdTerm = mulDivDown(secondTerm, firstTerm, 3 * WAD);
        return firstTerm + secondTerm + thirdTerm;
    }
}

library SharesMathLib {
    using MathLib for uint256;

    uint256 internal constant VIRTUAL_SHARES = 1e6;
    uint256 internal constant VIRTUAL_ASSETS = 1;

    function toSharesDown(uint256 assets, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return assets.mulDivDown(totalShares + VIRTUAL_SHARES, totalAssets + VIRTUAL_ASSETS);
    }

    function toAssetsDown(uint256 shares, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return shares.mulDivDown(totalAssets + VIRTUAL_ASSETS, totalShares + VIRTUAL_SHARES);
    }

    function toSharesUp(uint256 assets, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return assets.mulDivUp(totalShares + VIRTUAL_SHARES, totalAssets + VIRTUAL_ASSETS);
    }

    function toAssetsUp(uint256 shares, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return shares.mulDivUp(totalAssets + VIRTUAL_ASSETS, totalShares + VIRTUAL_SHARES);
    }
}

contract SequenceFixture {
    using MarketParamsLib for MarketParams;
    using MathLib for uint256;
    using SharesMathLib for uint256;
    using UtilsLib for uint256;

    error MarketStepBlocked(Id marketId, uint256 totalSupplyAssets, uint256 totalBorrowAssets);

    event AccrueInterest(Id indexed id, uint256 prevBorrowRate, uint256 interest, uint256 feeShares);

    address public feeRecipient;
    Id public lastMarketId;
    mapping(Id => Market) public market;
    mapping(Id => mapping(address => Position)) public position;

    uint256 private totalScore;
    bytes32 private lastDigest;

    function _simulatedMarket(Id id, address irm, uint256 ratePerSecond) internal view returns (Market memory m) {
        m = market[id];
        uint256 elapsed = block.timestamp.zeroFloorSub(m.lastUpdate);
        if (elapsed != 0 && m.totalBorrowAssets != 0 && irm != address(0)) {
            uint256 interest = uint256(m.totalBorrowAssets).wMulDown(ratePerSecond.wTaylorCompounded(elapsed));
            m.totalBorrowAssets += interest.toUint128();
            m.totalSupplyAssets += interest.toUint128();
            if (m.fee != 0) {
                uint256 feeAmount = interest.wMulDown(m.fee);
                uint256 feeShares =
                    feeAmount.toSharesDown(uint256(m.totalSupplyAssets).zeroFloorSub(feeAmount), m.totalSupplyShares);
                m.totalSupplyShares += feeShares.toUint128();
            }
        }
        ++m.lastUpdate;
    }

    function computeId(MarketParams memory marketParams) external pure returns (Id) {
        return marketParams.id();
    }

    function expectedMarketBalances(MarketParams memory marketParams, uint256 ratePerSecond)
        public
        view
        returns (uint256, uint256, uint256, uint256)
    {
        Id id = marketParams.id();
        Market memory m = _simulatedMarket(id, marketParams.irm, ratePerSecond);
        return (m.totalSupplyAssets, m.totalSupplyShares, m.totalBorrowAssets, m.totalBorrowShares);
    }

    function expectedTotalSupplyAssets(MarketParams memory marketParams, uint256 ratePerSecond)
        external
        view
        returns (uint256 totalSupplyAssets)
    {
        (totalSupplyAssets,,,) = expectedMarketBalances(marketParams, ratePerSecond);
    }

    function expectedSupplyAssets(MarketParams memory marketParams, address user, uint256 ratePerSecond)
        external
        view
        returns (uint256)
    {
        Id id = marketParams.id();
        uint256 supplyShares = position[id][user].supplyShares;
        (uint256 totalSupplyAssets, uint256 totalSupplyShares,,) = expectedMarketBalances(marketParams, ratePerSecond);
        return supplyShares.toAssetsDown(totalSupplyAssets, totalSupplyShares);
    }

    function expectedBorrowAssets(MarketParams memory marketParams, address user, uint256 ratePerSecond)
        external
        view
        returns (uint256)
    {
        Id id = marketParams.id();
        uint256 borrowShares = position[id][user].borrowShares;
        (,, uint256 totalBorrowAssets, uint256 totalBorrowShares) = expectedMarketBalances(marketParams, ratePerSecond);
        return borrowShares.toAssetsUp(totalBorrowAssets, totalBorrowShares);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 bucket = input & 0x3;
        address user = address(uint160(0x3000 | bucket));
        address feeRecip = address(uint160(0x6000 | ((input >> 2) & 0x3)));
        feeRecipient = feeRecip;

        uint256 supplyDelta = ((input & 0x3f) + 1) * 1000;
        uint256 borrowDelta = supplyDelta / 2;
        uint256 ratePerSecond = ((input & 0xf) + 1) * 1e8;

        MarketParams memory mp = MarketParams({
            loanToken: address(uint160(0x1000 | bucket)),
            collateralToken: address(uint160(0x2000 | bucket)),
            oracle: address(uint160(0x4000 | bucket)),
            irm: (input & 8) != 0 ? address(0) : address(uint160(0x5000 | bucket)),
            lltv: 800000000000000000 + bucket * 10000000000000000
        });
        Id id = mp.id();
        Market memory m = _simulatedMarket(id, mp.irm, ratePerSecond);

        uint256 mintedSupplyShares = supplyDelta.toSharesDown(m.totalSupplyAssets, m.totalSupplyShares);
        m.totalSupplyAssets += supplyDelta.toUint128();
        m.totalSupplyShares += mintedSupplyShares.toUint128();

        uint256 mintedBorrowShares = borrowDelta.toSharesUp(m.totalBorrowAssets, m.totalBorrowShares);
        m.totalBorrowAssets += borrowDelta.toUint128();
        m.totalBorrowShares += mintedBorrowShares.toUint128();

        m.fee = uint128(((input & 0x7) + 1) * 1e16);
        m.lastUpdate = uint128(block.timestamp.zeroFloorSub(5));
        uint128 stepTag = m.lastUpdate++;
        market[id] = m;

        Position memory pos = position[id][user];
        pos.supplyShares += mintedSupplyShares;
        pos.borrowShares += mintedBorrowShares.toUint128();
        pos.collateral += uint128(supplyDelta * 2);
        position[id][user] = pos;
        lastMarketId = id;

        if (input == 21) {
            revert MarketStepBlocked(id, m.totalSupplyAssets, m.totalBorrowAssets);
        }

        emit AccrueInterest(id, ratePerSecond, m.totalSupplyAssets, m.totalSupplyShares);

        uint256 summary;
        unchecked {
            summary =
                uint256(Id.unwrap(id)) +
                uint256(uint160(feeRecipient)) +
                uint256(m.totalSupplyAssets) +
                uint256(m.totalSupplyShares) +
                uint256(m.totalBorrowAssets) +
                uint256(m.totalBorrowShares) +
                pos.supplyShares +
                uint256(pos.borrowShares) +
                uint256(pos.collateral) +
                uint256(stepTag) +
                uint256(m.lastUpdate);
        }

        bytes32 digest = bytes32(
            uint256(Id.unwrap(id)) ^
            (summary << 16) ^
            (uint256(m.lastUpdate) << 8) ^
            uint256(stepTag)
        );
        uint256 metric = (uint256(digest) & 0xffffffff) + (summary & 0xffffffff);
        totalScore += metric;
        lastDigest = digest;
        require(input != 20, "MP: rollback");
        return totalScore;
    }

    function fail() external {
        feeRecipient = address(0xBEEF);
        totalScore += 999;
        revert("MP: fail");
    }

    function read() external view returns (uint256, bytes32, Id, address) {
        return (totalScore, lastDigest, lastMarketId, feeRecipient);
    }
}
