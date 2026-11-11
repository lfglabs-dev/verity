// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Storage array `push` once the length reaches 2^64: solc panics with 0x41 before it writes
/// the new length, for value and struct elements alike. `change(x)` with x % 4 == 0 raises
/// each array's length to 2^64 - 2 through a storage pointer (the StorageSlot pattern), so the
/// next two pushes onto it succeed and the third panics. Lengths only ever rise, so storage
/// past every length stays zero, as in any solc-compiled contract (`push()` relies on it).
contract SequenceFixture {
    struct Pair {
        uint128 low;
        uint256 high;
    }

    struct Word {
        uint256 value;
    }

    uint256 private constant NEAR_FULL = 2 ** 64 - 2;

    uint256[] private values;
    Pair[] private pairs;
    Pair[] private blanks;

    function wordAt(uint256 slot) private pure returns (Word storage word) {
        assembly {
            word.slot := slot
        }
    }

    function raise(uint256 slot) private {
        Word storage length = wordAt(slot);
        if (length.value < NEAR_FULL) {
            length.value = NEAR_FULL;
        }
    }

    function change(uint256 x) external {
        uint256 kind = x % 4;
        if (kind == 0) {
            raise(0);
            raise(1);
            raise(2);
        } else if (kind == 1) {
            values.push(x);
        } else if (kind == 2) {
            pairs.push(Pair(uint128(x), x + 1));
        } else {
            blanks.push();
        }
    }

    function fail() external pure {
        revert();
    }

    function read() external view returns (uint256, uint256, uint256, uint256, uint256, uint256) {
        uint256 n = values.length;
        uint256 m = pairs.length;
        return (
            n,
            m,
            blanks.length,
            n == 0 ? 0 : values[n - 1],
            m == 0 ? 0 : pairs[m - 1].low,
            m == 0 ? 0 : pairs[m - 1].high
        );
    }
}
