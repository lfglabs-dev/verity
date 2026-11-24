// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library ScanHelperLib {
    struct RangeIter {
        uint256 cursor;
        uint256 end;
    }

    struct MaskIter {
        uint256 mask;
    }

    function findMatchingWord(
        uint256[] memory words,
        uint256 start,
        uint256 bound,
        uint256 target
    ) internal pure returns (uint256) {
        for (uint256 i = start; i < bound; i++) {
            if (words[i] == target) {
                return i;
            }
        }
        return type(uint256).max;
    }

    function findFirstSetInRange(
        uint256 bitmap,
        uint256 startBit,
        uint256 count
    ) internal pure returns (bool found, uint256 bitIdx) {
        for (uint256 i = startBit; i < startBit + count; ++i) {
            if (((bitmap >> i) & 1) != 0) {
                return (true, i);
            }
        }
        return (false, 0);
    }

    function scanUncheckedStep(
        uint256 start,
        uint256 bound,
        uint256 divisor
    ) internal pure returns (uint256) {
        for (uint256 i = start; i < bound;) {
            if (i % divisor == 0) {
                return i;
            }
            unchecked {
                ++i;
            }
        }
        return 0;
    }

    function hasNextRange(RangeIter memory self) internal pure returns (bool) {
        return self.cursor < self.end;
    }

    function hasNextMask(MaskIter memory self) internal pure returns (bool) {
        return self.mask != 0;
    }

    function hasBits(uint256 mask) internal pure returns (bool) {
        return mask != 0;
    }
}

/// Synthetic clean-room fixture covering R2 & R4:
/// - R2: Helper `for`-loop early `return` with `uint256` bounds, non-zero start,
///   computed bounds, multi-return, void helper, and `unchecked { ++i; }` body step.
/// - R4: General boolean helper calls in `while` conditions (internal, library,
///   struct iterator `hasNext`, compound `&&`, checked-decrement fallback) and
///   `unchecked { --x; }` / `unchecked { ++i; }` inside `while` loop bodies.
contract HelperLoopAndWhileExt {
    using ScanHelperLib for ScanHelperLib.RangeIter;
    using ScanHelperLib for ScanHelperLib.MaskIter;
    using ScanHelperLib for uint256;

    uint256 internal recorded;
    uint256 internal tailHits;

    function _hasRemaining(uint256 remaining) internal pure returns (bool) {
        return remaining > 0;
    }

    function _isEligible(uint256 remaining) internal pure returns (bool) {
        if (remaining == 0) {
            return false;
        }
        return (remaining & 1) == 1 || remaining > 2;
    }

    function _voidScan(uint256 start, uint256 bound, uint256 stopAt) internal {
        for (uint256 i = start; i < bound; i++) {
            recorded += i;
            if (i == stopAt) {
                return;
            }
        }
        tailHits += 1;
    }

    function _helperWhileFind(uint256 remaining, uint256 want)
        internal
        pure
        returns (uint256)
    {
        uint256 acc = 0;
        while (_hasRemaining(remaining)) {
            acc += remaining;
            if (remaining == want) {
                return acc * 10 + remaining;
            }
            unchecked {
                --remaining;
            }
        }
        return acc;
    }

    function scanWords(uint256[] memory words, uint256 start, uint256 bound, uint256 target)
        external
        pure
        returns (uint256)
    {
        return ScanHelperLib.findMatchingWord(words, start, bound, target);
    }

    function scanBitmapRange(uint256 bitmap, uint256 startBit, uint256 count)
        external
        pure
        returns (bool, uint256)
    {
        return ScanHelperLib.findFirstSetInRange(bitmap, startBit, count);
    }

    function scanDivisible(uint256 start, uint256 bound, uint256 divisor)
        external
        pure
        returns (uint256)
    {
        return ScanHelperLib.scanUncheckedStep(start, bound, divisor);
    }

    function voidUint256Scan(uint256 start, uint256 bound, uint256 stopAt)
        external
        returns (uint256, uint256)
    {
        _voidScan(start, bound, stopAt);
        return (recorded, tailHits);
    }

    function whileUncheckedDecNeqZero(uint256 remaining) external pure returns (uint256 acc) {
        while (remaining != 0) {
            unchecked {
                acc += remaining;
                --remaining;
            }
        }
    }

    function whileUncheckedInc(uint256 start, uint256 limit) external pure returns (uint256 acc) {
        uint256 i = start;
        while (i < limit) {
            acc += i;
            unchecked {
                ++i;
            }
        }
    }

    function whileBoolHelperUncheckedDec(uint256 remaining) external pure returns (uint256 acc) {
        while (_hasRemaining(remaining)) {
            acc += remaining;
            unchecked {
                --remaining;
            }
        }
    }

    function whileLibHasBits(uint256 mask) external pure returns (uint256 count) {
        while (mask.hasBits()) {
            unchecked {
                ++count;
            }
            mask &= mask - 1;
        }
    }

    function whileRangeIter(uint256 start, uint256 end) external pure returns (uint256 acc) {
        ScanHelperLib.RangeIter memory it = ScanHelperLib.RangeIter({cursor: start, end: end});
        while (it.hasNextRange()) {
            acc += it.cursor;
            unchecked {
                ++it.cursor;
            }
        }
    }

    function whileMaskIter(uint256 mask) external pure returns (uint256 count) {
        ScanHelperLib.MaskIter memory it = ScanHelperLib.MaskIter({mask: mask});
        while (it.hasNextMask()) {
            unchecked {
                ++count;
            }
            it.mask &= it.mask - 1;
        }
    }

    function whileComplexHelperCheckedDec(uint256 remaining) external pure returns (uint256 acc) {
        while (_isEligible(remaining)) {
            acc += remaining;
            --remaining;
        }
    }

    function whileHelperEarlyReturn(uint256 remaining, uint256 want)
        external
        pure
        returns (uint256)
    {
        return _helperWhileFind(remaining, want);
    }
}
