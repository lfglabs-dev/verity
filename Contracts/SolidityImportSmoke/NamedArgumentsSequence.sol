// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library Scale {
    function scaled(uint256 value, uint256 factor, uint256 offset) internal pure returns (uint256) {
        return value * factor + offset;
    }
}

/// Named call arguments written in declaration order: an internal call, an attached
/// (`using for`) call, which names every parameter but the receiver, a struct constructor,
/// an event and a custom error. Two-argument calls take operands of one type, so binding by
/// position in any other order would still type-check and give other values.
contract SequenceFixture {
    using Scale for uint256;

    struct Entry {
        uint128 amount;
        uint64 stamp;
        bool flag;
    }

    uint256 private constant LIMIT = 2 ** 128;

    uint256 private value;
    Entry private last;

    error TooLarge(uint256 value, uint256 limit);

    event Changed(address indexed by, uint256 previous, uint256 next);

    function _combine(uint256 base, uint256 extra) internal pure returns (uint256) {
        return base * 2 + extra;
    }

    function change(uint256 x) external returns (uint256) {
        require(x < LIMIT, TooLarge({value: x, limit: LIMIT}));
        uint256 previous = value;
        value = _combine({base: x, extra: previous % 7});
        value = x.scaled({factor: 3, offset: value % 5});
        last = Entry({amount: uint128(x), stamp: uint64(block.timestamp), flag: x % 2 == 1});
        emit Changed({by: msg.sender, previous: previous, next: value});
        return value;
    }

    function fail() external view {
        require(value <= 15, "range");
    }

    function read() external view returns (uint256) {
        return value + last.amount + (last.flag ? 1 : 0) + last.stamp;
    }
}
