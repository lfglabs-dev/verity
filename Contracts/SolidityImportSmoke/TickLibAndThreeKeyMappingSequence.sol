// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

int256 constant LN_ONE_PLUS_DELTA = 0.004987541511039073e18; // floor(ln(1.005) * 1e18)
uint256 constant MAX_TICK = 6744;
uint256 constant PRICE_ROUNDING_STEP = 1e11;

library TickLib {
    using TickLib for uint256;

    error PriceGreaterThanOne();
    error TickOutOfRange();

    function divHalfDownUnchecked(uint256 x, uint256 d) internal pure returns (uint256) {
        unchecked {
            return (x + (d - 1) / 2) / d;
        }
    }

    function wExp(int256 x) internal pure returns (uint256) {
        unchecked {
            if (x < 0) {
                return 1e36 / wExp(-x);
            } else {
                int256 ln2 = 0.693147180559945309e18; // floor(ln(2) * 1e18)
                int256 offset = 0.32261121498945987e18;
                int256 q = (x + offset) / ln2;
                int256 r = x - q * ln2;
                int256 secondTerm = r * r / (2 * 1e18);
                int256 thirdTerm = secondTerm * r / (3 * 1e18);
                int256 expR = 1e18 + r + secondTerm + thirdTerm;
                return uint256(expR) << uint256(q);
            }
        }
    }

    function tickToPrice(uint256 tick) internal pure returns (uint256) {
        require(tick <= MAX_TICK, TickOutOfRange());
        unchecked {
            return uint256(1e36)
                    .divHalfDownUnchecked(1e18 + wExp(LN_ONE_PLUS_DELTA * (int256(MAX_TICK / 2) - int256(tick))))
                    .divHalfDownUnchecked(PRICE_ROUNDING_STEP) * PRICE_ROUNDING_STEP;
        }
    }

    function priceToTick(uint256 price, uint256 spacing) internal pure returns (uint256) {
        require(price <= 1e18, PriceGreaterThanOne());
        uint256 low = 0;
        uint256 high = MAX_TICK;
        while (low != high) {
            unchecked {
                uint256 mid = (low + high) / 2;
                if (tickToPrice(mid) < price) low = mid + 1;
                else high = mid;
            }
        }
        return (low + spacing - 1) / spacing * spacing;
    }
}

contract SequenceFixture {
    enum CreditSide {
        Lender,
        Borrower
    }

    struct Quota {
        uint128 limit;
        uint64 used;
        bool active;
    }

    uint16[4] private feeTiers;
    uint256[3] private epochCaps;
    mapping(CreditSide => mapping(address => mapping(address => uint256))) private nonces;
    mapping(bytes32 => mapping(address => mapping(uint256 => bool))) private approvals;
    mapping(bytes32 => mapping(address => mapping(uint256 => Quota))) private quotas;
    uint256 private lastPrice;
    uint256 private lastTick;

    function change(uint256 input) external returns (uint256, uint256) {
        if (input == 19) {
            return (TickLib.tickToPrice(MAX_TICK + 1), 0);
        }
        if (input == 21) {
            return (0, TickLib.priceToTick(1e18 + 1, 8));
        }

        uint256 rawTick = (input * 337) % (MAX_TICK + 1);
        uint256 spacing = (input % 2 == 0) ? 8 : 24;
        uint256 alignedTick = (rawTick / spacing) * spacing;
        uint256 price = TickLib.tickToPrice(alignedTick);
        uint256 recoveredTick = TickLib.priceToTick(price, spacing);
        lastPrice += price;
        lastTick += recoveredTick;

        uint256 idx4 = input % feeTiers.length;
        uint256 idx3 = input % epochCaps.length;
        feeTiers[0] = uint16(100 + (input % 50));
        feeTiers[1] = uint16(200 + (input % 50));
        feeTiers[2] = uint16(300 + (input % 50));
        feeTiers[3] = uint16(400 + (input % 50));
        delete feeTiers[1];
        feeTiers[idx4] = feeTiers[idx4] + uint16(recoveredTick % 100);
        uint16[4] memory snapFees = feeTiers;
        feeTiers[0] = uint16(snapFees[0] + uint16(snapFees.length));

        epochCaps[0] = 10 + (input % 7);
        epochCaps[1] = 20 + (input % 7);
        epochCaps[2] = 30 + (input % 7);
        if (input % 5 == 4) {
            delete epochCaps;
        }
        epochCaps[idx3] = epochCaps[idx3] + (price / 1e11 + epochCaps.length);
        uint256[3] memory snapCaps = epochCaps;

        address delegate = address(uint160(0xBEEF + (input % 3)));
        CreditSide side = (input % 2 == 0) ? CreditSide.Lender : CreditSide.Borrower;
        nonces[side][msg.sender][delegate] += 1;
        uint256 nAfterInc = ++nonces[side][msg.sender][delegate];
        if (input % 7 == 6) {
            delete nonces[CreditSide.Borrower][msg.sender][delegate];
        }

        bytes32 marketId = bytes32(uint256(0xA11CE + (input % 2)));
        uint256 bucket = input % 3;
        approvals[marketId][msg.sender][bucket] = (input % 3 != 0);
        if (input % 4 == 3) {
            delete approvals[marketId][msg.sender][(bucket + 1) % 3];
        }

        quotas[marketId][msg.sender][bucket] = Quota({
            limit: uint128(1000 + price / 1e12),
            used: uint64(recoveredTick + nAfterInc),
            active: true
        });
        Quota storage q = quotas[marketId][msg.sender][bucket];
        q.used += uint64(snapFees[idx4]);
        Quota memory qSnap = quotas[marketId][msg.sender][bucket];
        if (input % 6 == 5) {
            delete quotas[marketId][msg.sender][(bucket + 2) % 3];
        }

        require(input != 20, "ticklib 3key rollback");
        return (
            price + snapCaps[0] + snapCaps[1] + snapCaps[2] + uint256(qSnap.limit),
            recoveredTick + uint256(qSnap.used) + nonces[side][msg.sender][delegate]
        );
    }

    function fail() external {
        bytes32 marketId = bytes32(uint256(0xA11CE));
        feeTiers[0] = 999;
        epochCaps[0] = 888;
        nonces[CreditSide.Lender][msg.sender][msg.sender] = 777;
        quotas[marketId][msg.sender][0].limit = 666;
        lastPrice = TickLib.tickToPrice(MAX_TICK + 5);
    }

    function read() external view returns (uint256, uint256, uint256, uint256) {
        bytes32 marketId = bytes32(uint256(0xA11CE));
        address d0 = address(uint160(0xBEEF));
        address d1 = address(uint160(0xBEEF + 1));
        uint256 feeSummary =
            uint256(feeTiers[0]) +
            (uint256(feeTiers[1]) << 16) +
            (uint256(feeTiers[2]) << 32) +
            (uint256(feeTiers[3]) << 48);
        uint256 capSummary = epochCaps[0] + epochCaps[1] * 10 + epochCaps[2] * 100;
        uint256 nonceSummary =
            nonces[CreditSide.Lender][msg.sender][d0] +
            nonces[CreditSide.Borrower][msg.sender][d1] * 100 +
            (approvals[marketId][msg.sender][0] ? 10000 : 0) +
            (approvals[marketId][msg.sender][1] ? 20000 : 0);
        Quota storage q0 = quotas[marketId][msg.sender][0];
        uint256 quotaSummary =
            lastPrice + lastTick + uint256(q0.limit) + uint256(q0.used) + (q0.active ? 1 : 0);
        return (feeSummary, capSummary, nonceSummary, quotaSummary);
    }

    function quoteTickRoundtrip(uint256 tick, uint256 spacing) external pure returns (uint256, uint256) {
        uint256 boundedSpacing = spacing == 0 ? 8 : spacing;
        uint256 price = TickLib.tickToPrice(tick);
        uint256 recovered = TickLib.priceToTick(price, boundedSpacing);
        return (price, recovered);
    }
}
