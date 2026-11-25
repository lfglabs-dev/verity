// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Early `return` and `break` inside inlined helper `for` loops over `uint256` bounds (#2916):
// matches on the first, a middle or the last iteration, no match, `n == 0`, a large `uint256`
// bound that exits early, a storage write in every iteration before the match, a pre-declared
// counter, a named result read by the returned value, and a return inside an `unchecked`
// block of a loop that may also `break`.
contract SequenceFixture {
    uint256 private total;
    uint256 private hits;

    function _at(uint256 packed, uint256 i) private pure returns (uint32) {
        return uint32(packed >> (i * 32));
    }

    function _contains(uint256 packed, uint256 n, uint32 id) private pure returns (bool) {
        for (uint256 i = 0; i < n; ++i) {
            if (_at(packed, i) == id) return true;
        }
        return false;
    }

    function _containsTracked(uint256 packed, uint256 n, uint32 id) private returns (bool) {
        for (uint256 i = 0; i < n; ++i) {
            hits += 1;
            if (_at(packed, i) == id) return true;
        }
        return false;
    }

    function _byteAt(uint256 word, uint256 i) private pure returns (uint256) {
        return (word >> (i * 8)) & 0xff;
    }

    function _indexOf(uint256 word, uint256 n, uint256 needle) internal pure returns (uint256) {
        for (uint256 i = 0; i < n; i++) {
            if (_byteAt(word, i) == needle) {
                return i + 1;
            }
        }
        return 0;
    }

    function _hasByte(uint256 word, uint256 n, uint256 needle) internal returns (bool) {
        for (uint256 i = 0; i < n; ++i) {
            hits += 1;
            if (_byteAt(word, i) == needle) return true;
        }
        return false;
    }

    function _findStep(uint256 n, uint256 target) internal returns (uint256) {
        uint256 i;
        for (i = 0; i < n; i++) {
            hits += 1;
            if (i == target) {
                return i + 1;
            }
        }
        return i + 100000;
    }

    function _countBefore(uint256 n, uint256 stopAt) internal returns (uint256 count) {
        for (uint256 i = 0; i < n; ++i) {
            if (i == stopAt) {
                break;
            }
            hits += 1;
            count += 1;
        }
    }

    function _firstAbove(uint256 word, uint256 limit) internal pure returns (uint256 found) {
        found = 999;
        for (uint256 i = 0; i < 4; i++) {
            uint256 v = _byteAt(word, i);
            if (v > limit) {
                return v + found;
            }
        }
        found += 1;
    }

    function _sumUntil(uint256 n, uint256 cap) internal pure returns (uint256 acc) {
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
        uint256 word = x >> 16;
        uint256 n = x % 8;
        uint256 needle = (x >> 8) & 0xff;
        uint256 r = _indexOf(word, n, needle) * 10000;
        if (_hasByte(word, n, needle)) {
            r += 7;
        }
        if (_contains(word, n, uint32(needle))) {
            r += 13;
        }
        uint256 span = (x >> 24) % 301;
        uint256 target = (x >> 40) % 305;
        r += _findStep(span, target);
        uint256 largeBound = (x & 7) == 7 ? 2000 : span;
        uint256 cb = _countBefore(largeBound, (x >> 56) % 12);
        r += cb * 11;
        if ((x & 7) == 7) {
            if (_containsTracked(word, 2000, 0)) {
                r += 29;
            }
        }
        r += _firstAbove(word, x & 0xff) * 3;
        r += _sumUntil((x >> 248) + ((x >> 64) & 0x1ff), (x >> 16) & 0xff);
        total += r;
        return r;
    }

    function scanLarge(uint256 packed, uint256 n, uint32 id) external returns (bool) {
        bool ok = _containsTracked(packed, n, id);
        if (ok) {
            total += 1;
        }
        return ok;
    }

    function countUntilBreak(uint256 n, uint256 stopAt) external returns (uint256) {
        uint256 c = _countBefore(n, stopAt);
        total += c;
        return c;
    }

    function fail() external {
        _hasByte(0, 300, 1);
        revert();
    }

    function read() external view returns (uint256, uint256) {
        return (total, hits);
    }
}
