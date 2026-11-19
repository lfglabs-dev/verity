// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library Scale {
    function scaled(uint256 value, uint256 factor, uint256 offset) internal pure returns (uint256) {
        return value * factor + offset;
    }
}

/// In-order and reordered internal and attached calls, a single panicking operand,
/// and reordered event topics/data. The struct constructor and custom error keep their
/// declaration-order controls; swapping the helper's same-typed operands changes its result.
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

    function _advance() internal returns (uint256) {
        value += 1;
        return value;
    }

    function change(uint256 x) external returns (uint256) {
        require(x < LIMIT, TooLarge({value: x, limit: LIMIT}));
        uint256 previous = value;
        value = _combine({base: x, extra: previous % 7});
        value = x.scaled({offset: value % 5, factor: 3});
        value = _combine({extra: 12 / x, base: value});
        uint256 observed = _combine({extra: _advance(), base: 3});
        last = Entry({amount: uint128(x), stamp: uint64(block.timestamp), flag: x % 2 == 1});
        emit Changed({next: value, previous: previous, by: msg.sender});
        return observed;
    }

    function fail() external view {
        require(value <= 15, "range");
    }

    function read() external view returns (uint256) {
        return value + last.amount + (last.flag ? 1 : 0) + last.stamp;
    }
}
