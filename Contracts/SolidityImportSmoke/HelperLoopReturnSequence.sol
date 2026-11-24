// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Early `return` inside inlined helper `for` loops: a match on the first, a middle or the
// last iteration, or no match; a storage write in every iteration before the match; a
// named result read by the returned value; and a return inside an `unchecked` block of a
// loop that may also `break`.
contract SequenceFixture {
    uint256 private total;
    uint256 private hits;

    function _at(uint256 packed, uint256 i) private pure returns (uint256) {
        return (packed >> (i * 8)) & 0xff;
    }

    function _indexOf(uint256 packed, uint8 n, uint256 needle) internal pure returns (uint256) {
        for (uint256 i = 0; i < n; i++) {
            if (_at(packed, i) == needle) {
                return i + 1;
            }
        }
        return 0;
    }

    function _contains(uint256 packed, uint8 n, uint256 needle) internal returns (bool) {
        for (uint256 i = 0; i < n; ++i) {
            hits += 1;
            if (_at(packed, i) == needle) return true;
        }
        return false;
    }

    function _firstAbove(uint256 packed, uint256 limit) internal pure returns (uint256 found) {
        found = 999;
        for (uint256 i = 0; i < 4; i++) {
            uint256 v = _at(packed, i);
            if (v > limit) {
                return v + found;
            }
        }
        found += 1;
    }

    function _sumUntil(uint8 n, uint256 cap) internal pure returns (uint256 acc) {
        for (uint256 i = 0; i < n; i++) {
            if (i == 9) {
                break;
            }
            acc += i * i;
            unchecked {
                if (acc > cap) {
                    return acc - cap;
                }
            }
        }
        acc += 1000;
    }

    function change(uint256 x) external returns (uint256) {
        uint256 packed = x >> 16;
        uint8 n = uint8(x % 8);
        uint256 needle = (x >> 8) & 0xff;
        uint256 r = _indexOf(packed, n, needle) * 10000;
        if (_contains(packed, n, needle)) {
            r += 7;
        }
        r += _firstAbove(packed, x & 0xff) * 3;
        r += _sumUntil(uint8(x >> 248), (x >> 16) & 0xff);
        total += r;
        return r;
    }

    function fail() external {
        _contains(0, 5, 1);
        revert();
    }

    function read() external view returns (uint256, uint256) {
        return (total, hits);
    }
}
