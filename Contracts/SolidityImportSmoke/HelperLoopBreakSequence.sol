// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `break` / `continue` inside inlined helper loops: a `for` that breaks on a running sum,
// nested `for` loops where the inner `break` / `continue` leave only the inner loop, a
// `while` that breaks after an early `return`, and a void helper that writes storage
// until it breaks.
contract SequenceFixture {
    uint256 private total;
    uint256 private hits;

    function _sumUpTo(uint256 n, uint256 cap) internal pure returns (uint256 acc) {
        for (uint256 i = 0; i < n; i++) {
            acc += i;
            if (acc >= cap) {
                break;
            }
        }
    }

    function _grid(uint256 n) internal pure returns (uint256 acc) {
        for (uint256 i = 0; i < n; i++) {
            if (i % 4 == 1) {
                continue;
            }
            for (uint256 j = 0; j < 10; j++) {
                if (j > i) {
                    break;
                }
                if (j % 2 == 0) {
                    continue;
                }
                acc += i * j;
            }
            if (acc > 500) {
                break;
            }
            acc += 1;
        }
    }

    function _lowBits(uint256 v) internal pure returns (uint256 count) {
        if (v == 0) {
            return 999;
        }
        while (v != 0) {
            if (v & 3 == 3) {
                break;
            }
            count += 1;
            v >>= 1;
        }
    }

    function _record(uint256 n) internal {
        for (uint256 i = 0; i < n; i++) {
            if (i == 6) {
                break;
            }
            hits += 1;
        }
    }

    function change(uint256 x) external returns (uint256) {
        _record(x % 9);
        total += _sumUpTo(x % 50, x % 300) + _grid(x % 13) + _lowBits(x % 4096);
        return total;
    }

    function fail() external {
        _record(20);
        revert();
    }

    function read() external view returns (uint256, uint256) {
        return (total, hits);
    }
}
