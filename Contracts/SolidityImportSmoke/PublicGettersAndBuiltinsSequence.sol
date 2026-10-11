// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IERC4626Like {
    function asset() external view returns (address);
}

contract SequenceFixture is IERC4626Like {
    error VaultStepBlocked(uint256 input, bytes32 digest, uint256 historyLen);

    struct EpochState {
        uint64 id;
        uint192 cap;
        address manager;
        bool active;
    }

    struct Checkpoint {
        uint48 timestamp;
        uint208 amount;
    }

    struct Position {
        uint128 shares;
        uint64 unlockAt;
        bool locked;
    }

    uint256 public constant VERSION = 42;
    string public constant VAULT_NAME = "ParetoCreditVault";
    string private constant ERR_PAUSED = "CV: paused";
    string private constant ERR_BLOCKED = "CV: blocked";
    string private constant ERR_ROLLBACK = "CV: rollback";

    address public override asset;
    bool public paused;
    EpochState public currentEpoch;
    Checkpoint[] public history;
    uint256[3] public tiers;
    mapping(address => Position) public positions;
    mapping(bool => mapping(address => bool)) public isWhitelister;
    mapping(bool => mapping(address => mapping(address => uint256))) public nonces;
    mapping(address => uint256[2]) public limits;

    uint256 private totalScore;
    bytes32 private lastDigest;

    function _checkedScale(uint256 raw, uint256 mode) private view returns (uint256) {
        if (mode == 99) {
            revert(ERR_PAUSED);
        } else if (mode == 98) {
            revert("CV: bad mode");
        } else if (mode == 97) {
            revert();
        }
        require(mode != 96, ERR_BLOCKED);
        if (paused) {
            return raw + VERSION;
        }
        return raw * (mode + 1) + VERSION;
    }

    function change(uint256 input) external returns (uint256) {
        uint256 branch = input % 4;
        address user = address(uint160(0x3000 | (input & 0x3)));
        address delegate = address(uint160(0x4000 | ((input >> 2) & 0x3)));
        uint256 amount = ((input & 0x3f) + 1) * 10;

        if (branch == 0) {
            asset = address(uint160(0xA000 | (input & 0xf)));
            paused = (input & 4) != 0;
            currentEpoch = EpochState({
                id: uint64(history.length + 1),
                cap: uint192(amount * 100),
                manager: delegate,
                active: !paused
            });
            history.push(Checkpoint({
                timestamp: uint48(block.timestamp),
                amount: uint208(amount)
            }));
            tiers[0] = amount;
            tiers[1] = amount * 2;
            tiers[2] = amount * 3;
            positions[user] = Position({
                shares: uint128(amount),
                unlockAt: uint64(block.timestamp + 3600),
                locked: (input & 8) != 0
            });
            isWhitelister[true][delegate] = true;
            nonces[true][user][delegate] += 1;
            limits[user][0] = amount + 5;
            limits[user][1] = amount + 15;
        } else if (branch == 1) {
            paused = false;
            Position storage pos = positions[user];
            pos.shares += uint128(amount / 2);
            pos.locked = (input & 1) == 1;
            tiers[input % 3] = tiers[input % 3] + amount;
            isWhitelister[false][delegate] = pos.locked;
            nonces[false][user][delegate] += 2;
            limits[user][input & 1] = limits[user][input & 1] + amount;
        } else if (branch == 2) {
            currentEpoch.cap += uint192(amount);
            currentEpoch.active = (input & 1) == 0;
            history.push(Checkpoint({
                timestamp: uint48(block.timestamp + (input & 0xff)),
                amount: uint208(amount + VERSION)
            }));
        } else {
            paused = (input & 2) != 0;
            tiers[2] = _checkedScale(amount, input & 3);
            limits[delegate][0] = tiers[2];
        }

        uint256 scaled = _checkedScale(amount, branch);
        uint256 summary;
        unchecked {
            summary =
                VERSION +
                uint256(uint160(asset)) +
                (paused ? 1 : 0) +
                uint256(currentEpoch.id) +
                uint256(currentEpoch.cap) +
                uint256(uint160(currentEpoch.manager)) +
                (currentEpoch.active ? 1 : 0) +
                history.length +
                tiers[0] +
                tiers[1] +
                tiers[2] +
                uint256(positions[user].shares) +
                uint256(positions[user].unlockAt) +
                (positions[user].locked ? 1 : 0) +
                (isWhitelister[true][delegate] ? 1 : 0) +
                nonces[true][user][delegate] +
                nonces[false][user][delegate] +
                limits[user][0] +
                limits[user][1] +
                scaled;
        }

        uint256 hLen = history.length;
        bytes32 digest = bytes32(
            (summary << 32) ^
            (hLen << 16) ^
            (uint256(currentEpoch.id) << 8) ^
            tiers[0]
        );

        if (input == 21) {
            revert VaultStepBlocked(input, digest, hLen);
        }

        uint256 metric = (uint256(digest) & 0xffffffff) + summary;
        totalScore += metric;
        lastDigest = digest;
        require(input != 20, ERR_ROLLBACK);
        return totalScore;
    }

    function probeBuiltins(uint256 mode, uint256 value) external view returns (uint256) {
        uint256 scaled = _checkedScale(value, mode);
        require(value != 77, ERR_BLOCKED);
        return scaled + tiers[mode % 3];
    }

    function fail() external {
        asset = address(0xBEEF);
        paused = true;
        tiers[0] = 999;
        history.push(Checkpoint({timestamp: uint48(block.timestamp), amount: 777}));
        revert(ERR_PAUSED);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        uint256 summary;
        unchecked {
            summary =
                VERSION +
                uint256(uint160(asset)) +
                (paused ? 1 : 0) +
                uint256(currentEpoch.id) +
                uint256(currentEpoch.cap) +
                history.length +
                tiers[0] +
                tiers[1] +
                tiers[2];
        }
        return (totalScore, lastDigest, summary);
    }
}
