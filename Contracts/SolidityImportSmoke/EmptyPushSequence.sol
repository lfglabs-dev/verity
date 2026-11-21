// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Empty storage array `push()` over storage that is not zero. solc's push helpers grow the
/// length and write nothing, so the new element is whatever its slot already held. That slot
/// is non-zero once a length is lowered over written elements: `change(x)` with x % 4 == 0
/// lowers the three lengths to at most (x / 4) % 3 through a storage pointer (the StorageSlot
/// pattern), leaving the elements past them in place; when (x / 12) % 2 == 1 it also fills the
/// first word of the struct element at that index, padding included. `push(v)` then writes `v`
/// into its lane (neighbouring packed lanes and struct padding keep their bits), `push()` writes
/// nothing, and `x = a.push()` reads the stale element.
contract SequenceFixture {
    struct Pair {
        uint128 low;
        uint256 high;
    }

    struct Word {
        uint256 value;
    }

    uint256[] private words;
    uint64[] private lanes;
    Pair[] private pairs;
    uint256 private last;
    uint256 private lastWord;

    function wordAt(uint256 slot) private pure returns (Word storage word) {
        assembly {
            word.slot := slot
        }
    }

    function lower(uint256 slot, uint256 keep) private {
        Word storage length = wordAt(slot);
        if (length.value > keep) {
            length.value = keep;
        }
    }

    function change(uint256 x) external {
        uint256 kind = x % 4;
        if (kind == 0) {
            uint256 keep = (x / 4) % 3;
            lower(0, keep);
            lower(1, keep);
            lower(2, keep);
            if ((x / 12) % 2 == 1) {
                uint256 pairData = uint256(keccak256(abi.encode(uint256(2))));
                Word storage pairWord = wordAt(pairData + 2 * keep);
                pairWord.value = type(uint256).max - x;
            }
        } else if (kind == 1) {
            words.push(x);
            lanes.push(uint64(x));
            pairs.push(Pair(uint128(x), x + 1));
        } else if (kind == 2) {
            words.push();
            lanes.push();
            pairs.push();
        } else {
            last = lanes.push();
            lastWord = words.push();
        }
    }

    function fail() external pure {
        revert();
    }

    function read()
        external
        view
        returns (uint256, uint256, uint256, uint256, uint256, uint256, uint256, uint256)
    {
        uint256 n = words.length;
        uint256 m = lanes.length;
        uint256 k = pairs.length;
        return (
            n == 0 ? 0 : words[n - 1],
            m == 0 ? 0 : lanes[m - 1],
            k == 0 ? 0 : pairs[k - 1].low,
            k == 0 ? 0 : pairs[k - 1].high,
            last,
            lastWord,
            n,
            m + k
        );
    }
}
