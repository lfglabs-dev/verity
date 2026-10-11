// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

uint256 constant WAD = 1e18;
uint256 constant CBP = 1e12;

library MathLib {
    function mulDivDown(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y) / d;
    }

    function mulDivUp(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y + (d - 1)) / d;
    }

    function zeroFloorSub(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := mul(gt(x, y), sub(x, y))
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
}

contract SequenceFixture {
    using MathLib for uint256;
    using MathLib for uint128;
    using UtilsLib for uint128;

    error MarketNotCreated();
    error PositionStepBlocked(bytes32 id, address user, uint128 credit);

    event UpdatePosition(
        bytes32 indexed id,
        address indexed user,
        uint256 creditDecrease,
        uint256 pendingFeeDecrease,
        uint256 accruedFee
    );

    struct Position {
        uint128 credit;
        uint128 pendingFee;
        uint128 lastAccrual;
        uint128[2] collateral;
    }

    struct MarketState {
        uint128 lossFactor;
        uint16 settlementFeeCbp0;
        uint16 settlementFeeCbp1;
        uint16 settlementFeeCbp2;
        uint8 tickSpacing;
    }

    struct SummaryCard {
        uint128 totalCredited;
        uint64 activeCount;
        uint16[2] bandCounts;
    }

    struct BucketView {
        uint128 shareTotal;
        uint64 tag;
        uint32[2] tiers;
    }

    address private feeRecipient;
    bytes32 private activeMarketId;
    SummaryCard public summaryCard;
    mapping(bytes32 => BucketView) public bucketView;
    mapping(bytes32 id => MarketState) private marketState;
    mapping(bytes32 id => mapping(address user => Position)) public position;

    uint256 private totalScore;
    bytes32 private lastDigest;

    function collateral(bytes32 id, address user, uint256 index) external view returns (uint128) {
        return position[id][user].collateral[index];
    }

    function settlementFee(bytes32 id, uint256 timeToMaturity) public view returns (uint256) {
        MarketState storage _marketState = marketState[id];
        require(_marketState.tickSpacing > 0, MarketNotCreated());

        if (timeToMaturity >= 30 days) return _marketState.settlementFeeCbp2 * CBP;

        (uint256 start, uint256 end, uint256 feeLower, uint256 feeUpper) =
            timeToMaturity < 1 days ? (0 days,  1 days, _marketState.settlementFeeCbp0 * CBP, _marketState.settlementFeeCbp1 * CBP) :
                                      (1 days, 30 days, _marketState.settlementFeeCbp1 * CBP, _marketState.settlementFeeCbp2 * CBP);

        return (feeLower * (end - timeToMaturity) + feeUpper * (timeToMaturity - start)) / (end - start);
    }

    function updatePositionView(bytes32 id, address user, uint256 maturity)
        public
        view
        returns (uint128, uint128, uint128)
    {
        Position storage _position = position[id][user];
        uint128 _credit = _position.credit;
        uint256 postSlashCredit = uint256(_credit).mulDivDown(
            type(uint128).max - marketState[id].lossFactor,
            type(uint128).max
        );
        uint128 _pendingFee = _position.pendingFee;
        uint256 postSlashPendingFee =
            _credit > 0 ? _pendingFee - uint256(_pendingFee).mulDivUp(_credit - postSlashCredit, _credit) : 0;
        uint256 accrualEnd = UtilsLib.min(block.timestamp, maturity);
        uint128 _lastAccrual = _position.lastAccrual;
        uint128 fee = (_lastAccrual < maturity && accrualEnd >= _lastAccrual)
            ? uint128(postSlashPendingFee.mulDivDown(accrualEnd - _lastAccrual, maturity - _lastAccrual))
            : 0;
        return (uint128(postSlashCredit) - fee, uint128(postSlashPendingFee) - fee, fee);
    }

    function change(uint256 input) external returns (uint256) {
        bytes32 id = bytes32((input + 1) & 1);
        address user = msg.sender;
        address recip = address(0x6000);
        feeRecipient = recip;
        activeMarketId = id;

        MarketState storage ms = marketState[id];
        if (ms.tickSpacing == 0) {
            ms.tickSpacing = 10;
            ms.lossFactor = uint128((input & 0xf) * 1_000);
            ms.settlementFeeCbp0 = 10;
            ms.settlementFeeCbp1 = 25;
            ms.settlementFeeCbp2 = 60;
        } else {
            ms.lossFactor += uint128((input & 0x7) * 100);
        }

        Position storage pos = position[id][user];
        uint128 addedCredit = uint128(((input & 0x3f) + 10) * 1_000);
        uint128 addedFee = uint128(((input & 0xf) + 2) * 100);
        uint256 slotIdx = input & 1;
        pos.collateral[slotIdx] = uint128(((input & 0x1f) + 1) * 200);
        uint256 weightSum = uint256(pos.collateral[slotIdx]) * (slotIdx + 1);

        uint256 maturity = block.timestamp + ((input % 5) + 1) * 10 days;
        (uint128 viewCredit, uint128 viewPendingFee, uint128 accruedFee) = updatePositionView(id, user, maturity);
        uint128 newCredit = viewCredit + addedCredit;
        uint128 newPendingFee = viewPendingFee + addedFee;

        pos.credit = newCredit;
        pos.pendingFee = newPendingFee;
        pos.lastAccrual = uint128(block.timestamp.zeroFloorSub(10));

        if (input == 21) {
            revert PositionStepBlocked(id, user, newCredit);
        }

        emit UpdatePosition(id, user, addedCredit, addedFee, accruedFee);

        // Storage-variable key preludes in 2-key and 1-key struct member writes (=, delete, op=, ++):
        position[id][feeRecipient].credit = 100;
        position[id][feeRecipient].credit += accruedFee + 1;
        delete position[id][feeRecipient].pendingFee;

        bucketView[activeMarketId].tag = 10;
        uint64 prevRecipDebt = bucketView[activeMarketId].tag++;
        uint128 nextRecipBitmap = ++bucketView[activeMarketId].shareTotal;
        bucketView[activeMarketId].tiers[input & 1] = uint32(newCredit & 0xffff);

        summaryCard.totalCredited += newCredit;
        summaryCard.activeCount += 1;
        summaryCard.bandCounts[input & 1] = uint16((accruedFee & 0xff) + 1);

        uint256 timeToMat = ((input % 3) * 15 days) + 12 hours;
        uint256 sFee = settlementFee(id, timeToMat);

        uint256 summary;
        unchecked {
            summary =
                uint256(newCredit) +
                uint256(newPendingFee) +
                uint256(accruedFee) +
                uint256(position[id][feeRecipient].credit) +
                uint256(prevRecipDebt) +
                uint256(nextRecipBitmap) +
                sFee +
                weightSum;
        }

        bytes32 digest = bytes32(
            uint256(id) ^
            (summary << 12) ^
            (sFee << 4) ^
            weightSum
        );
        uint256 metric = (uint256(digest) & 0xffffffff) + (summary & 0xffffffff);
        totalScore += metric;
        lastDigest = digest;
        require(input != 20, "MPF: rollback");
        return totalScore;
    }

    function fail() external {
        feeRecipient = address(0xBEEF);
        totalScore += 777;
        revert("MPF: fail");
    }

    function read() external view returns (uint256, bytes32, bytes32, address) {
        return (totalScore, lastDigest, activeMarketId, feeRecipient);
    }
}
