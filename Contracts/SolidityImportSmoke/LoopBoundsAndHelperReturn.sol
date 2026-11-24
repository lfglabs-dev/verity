// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Synthetic fixture covering non-zero `for` loop bounds (constant, variable,
/// computed, pre-declared, narrow-counter wrap, decrementing) and early
/// `return` / `break` / `continue` inside inlined helper `for`, nested `for`,
/// `while`, and void helper loops.
contract LoopBoundsAndHelperReturn {
    uint256 internal logSum;
    uint256 internal tailMarks;

    function sumRange(uint256 start, uint256 end) external pure returns (uint256 total) {
        for (uint256 i = start; i < end; ++i) {
            total += i;
        }
    }

    function sumFromConst(uint256 end) external pure returns (uint256 total) {
        for (uint256 i = 2; i < end; ++i) {
            total += i;
        }
    }

    function sumFromExpr(uint256 base, uint256 end) external pure returns (uint256 total) {
        for (uint256 i = base + 1; i < end; ++i) {
            total += i;
        }
    }

    function predeclaredRange(uint256 start, uint256 end) external pure returns (uint256, uint256) {
        uint256 total = 0;
        uint256 i;
        for (i = start; i < end; ++i) {
            total += i;
        }
        return (total, i);
    }

    function narrowStartWrap(uint8 start, uint256 end) external pure returns (uint256 total) {
        for (uint8 i = start; i < end; ++i) {
            total += i;
        }
    }

    function sumDown(uint256 len, uint256 low) external pure returns (uint256 acc) {
        for (uint256 i = len; i > low; --i) {
            acc += i;
        }
    }

    function _findDown(uint8 len, uint256 target) internal pure returns (uint256) {
        for (uint256 i = len; i > 0; --i) {
            if (i == target) {
                return i * 10;
            }
        }
        return 999;
    }

    function helperDecrementReturn(uint8 len, uint256 target) external pure returns (uint256) {
        return _findDown(len, target);
    }

    function _scanFromOne(uint8 limit, uint256 skip, uint256 stopAt, uint256 pick)
        internal
        pure
        returns (uint256)
    {
        uint256 acc = 0;
        for (uint256 i = 1; i < limit; ++i) {
            if (i == skip) {
                continue;
            }
            if (i == pick) {
                return acc + i * 100;
            }
            if (i == stopAt) {
                break;
            }
            acc += i;
        }
        return acc;
    }

    function helperNonZeroControl(uint8 limit, uint256 skip, uint256 stopAt, uint256 pick)
        external
        pure
        returns (uint256)
    {
        return _scanFromOne(limit, skip, stopAt, pick);
    }

    function _findPair(uint8 rows, uint256 want) internal pure returns (uint256) {
        uint256 visited = 0;
        for (uint256 i = 1; i < rows; ++i) {
            for (uint256 j = 0; j < 4; ++j) {
                visited += 1;
                if (i * 10 + j == want) {
                    return visited * 1000 + i * 10 + j;
                }
            }
        }
        return visited;
    }

    function helperNestedReturn(uint8 rows, uint256 want) external pure returns (uint256) {
        return _findPair(rows, want);
    }

    function _whileReturn(uint256 v, uint256 stopStep) internal pure returns (uint256 steps) {
        while (v != 0) {
            steps += 1;
            if (steps == stopStep) {
                return steps * 100 + v;
            }
            v >>= 1;
        }
        steps += 10;
    }

    function helperWhileReturn(uint256 v, uint256 stopStep) external pure returns (uint256) {
        return _whileReturn(v, stopStep);
    }

    function _whileTrueReturn(uint256 v, uint256 stopStep) internal pure returns (uint256) {
        uint256 steps = 0;
        while (true) {
            steps += 1;
            if (steps == stopStep) {
                return steps * 50 + v;
            }
            v /= 2;
            if (v == 0) break;
        }
        return steps;
    }

    function helperWhileTrueReturn(uint256 v, uint256 stopStep) external pure returns (uint256) {
        return _whileTrueReturn(v, stopStep);
    }

    function _voidForReturn(uint8 n, uint256 hit) internal {
        for (uint256 i = 1; i < n; ++i) {
            logSum += i;
            if (i == hit) {
                return;
            }
        }
        tailMarks += 1;
    }

    function voidForEarlyReturn(uint8 n, uint256 hit) external returns (uint256, uint256) {
        _voidForReturn(n, hit);
        return (logSum, tailMarks);
    }

    function _voidWhileReturn(uint256 v, uint256 hit) internal {
        uint256 step = 0;
        while (v != 0) {
            step += 1;
            logSum += step;
            if (step == hit) {
                return;
            }
            v >>= 1;
        }
        tailMarks += 1;
    }

    function voidWhileEarlyReturn(uint256 v, uint256 hit) external returns (uint256, uint256) {
        _voidWhileReturn(v, hit);
        return (logSum, tailMarks);
    }
}
